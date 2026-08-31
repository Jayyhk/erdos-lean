import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace Erdos43

/-
# Problem Description

Erdős Problem 43. If `A, B ⊆ {1, …, N}` are Sidon sets with `(A - A) ∩ (B - B) = {0}`, is
`C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1)`, where `f(N)` is the largest size of a Sidon set in
`{1, …, N}`? And if `|A| = |B|`, can the bound be improved to
`C(|A|,2) + C(|B|,2) ≤ (1 - c + o(1)) C(f(N),2)` for some `c > 0`? `erdos_43` answers both in
the negative.

Erdős offered $100 for the first question in [Er95]; see also [Er82f, p.114]. The two
questions are `erdos_43_question_one` and `erdos_43_question_two` below, and `erdos_43` is
their conjunction. The `O(1)` is a constant `C` independent of `N`, the `o(1)` a function
`o =o[atTop] 1`, and `f N` is `Finset.maxSidonSubsetCard (Finset.Icc 1 N)`, the supremum of
`B.card` over Sidon subsets `B ⊆ {1, …, N}`.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos43.lean` together with the modules of
`src/latest/ErdosProblems/Erdos43/`. Those files are concatenated here in dependency order,
with their project-internal imports removed so that `Mathlib` is the only import, each
module's contents kept in a `section` carrying its own `open` lines, the whole wrapped once in
`namespace Erdos43`, and the upstream trust-base print lines and trailing `alias`es removed.
The two parts are renamed from `not_erdos_43` and `not_erdos_43_part_ii` (upstream
`erdos_43.parts.i` and `erdos_43.parts.ii`). No mathematical content is changed.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos42.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 42.
https://www.erdosproblems.com/forum/thread/42

Informal authors:
- GPT-5.5 Pro
- Harjas Sandhu

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex 5.5
- GPT-5.5 Pro
- Pawan Sasanka Ammanamanchi

URLs:
- https://www.erdosproblems.com/forum/thread/42#post-6370
- https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P42/CompactCayley/Proof.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/42.lean
- https://raw.githubusercontent.com/Shashi456/erdos-formalizations/refs/heads/main/Erdos/P42/CompactCayley/Proof.lean
-/
/-
**STANDALONE FLAT BUNDLE** of Erdős Problem #42 — compact-Cayley route.

This file is generated from the modular Route B files under `Erdos/P42` and
contains the assumption-free proof of `Erdos42.CompactCayley.compact_cayley_clique`.
Project-local imports are deliberately flattened; only Mathlib imports remain.
-/

attribute [local instance] Classical.propDecidable

/-!
Trust boundary:
  Mathlib/Lean core only (`propext`, `Classical.choice`, `Quot.sound`).
-/

/-! =============================================================
    Section from: Erdos/P42/Common.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared finite-combinatorial primitives.

`DiffFinset`, `SymmetricFinset`, `CliqueInCayley`, `AvoidsNonzeroDiff`, plus
tiny lemmas that both the Fourier-positive and compact-Cayley routes use. We
work with `Finset` rather than `Set` because Lean's `Set ℕ` subtraction is
truncated.
-/

namespace Erdos42

open Finset

/-- Difference set of two `Finset`s: image of `(a, b) ↦ a - b` over `A ×ˢ B`. -/
def DiffFinset {α : Type*} [DecidableEq α] [Sub α] (A B : Finset α) : Finset α :=
  (A ×ˢ B).image (fun ab => ab.1 - ab.2)

@[simp] lemma mem_diffFinset {α : Type*} [DecidableEq α] [Sub α]
    {A B : Finset α} {x : α} :
    x ∈ DiffFinset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a - b = x := by
  simp [DiffFinset, Finset.mem_image, Finset.mem_product, and_assoc]

/-- A `Finset` is symmetric under negation. -/
def SymmetricFinset {α : Type*} [Neg α] (S : Finset α) : Prop :=
  ∀ x, x ∈ S ↔ -x ∈ S

/-- A `Finset C` is a clique in the Cayley graph on `ZMod p` with allowed
difference set `T`: every pair of distinct vertices in `C` has its difference
in `T`. -/
def CliqueInCayley {p : ℕ} (T C : Finset (ZMod p)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → x - y ∈ T

/-- `A` and `B` share no nonzero difference. -/
def AvoidsNonzeroDiff {α : Type*} [DecidableEq α] [Zero α] [Sub α]
    (A B : Finset α) : Prop :=
  ∀ d ∈ DiffFinset A A, d ∈ DiffFinset B B → d = 0

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/Sidon.lean
    ============================================================= -/

/-
Erdős Problem 42 — Sidon predicates and the elementary cardinality / difference
lemmas every route depends on.

We define `IsSidonInt` over `Finset ℤ` (the natural setting for the analytic
proof) and `IsSidonNat` over `Finset ℕ` / `Set ℕ` (the FC-aligned setting).
Bridge lemmas live in `FC/Local.lean`.
-/

namespace Erdos42

open Finset

/-- A `Finset ℤ` is Sidon iff all unordered pair-sums are distinct, i.e. no
nontrivial additive collision `a₁ + a₂ = a₃ + a₄` with `{a₁, a₂} ≠ {a₃, a₄}`. -/
def IsSidonInt (A : Finset ℤ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-- A `Finset ℕ` is Sidon under the same rule. -/
def IsSidonNat (A : Finset ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

lemma isSidonInt_empty : IsSidonInt ∅ := by
  intro a₁ ha₁
  simp at ha₁

lemma IsSidonInt.mono {A B : Finset ℤ} (hB : IsSidonInt B) (hAB : A ⊆ B) :
    IsSidonInt A := by
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  exact hB (hAB ha₁) (hAB ha₂) (hAB ha₃) (hAB ha₄) hsum

/-! ## Elementary cardinality bounds (TODO) -/

/-- For `A ⊆ {1, …, N}` Sidon, the nonzero differences `(A - A) \ {0}` have
cardinality at most `2N - 2` (equals `|A|(|A|-1)`). -/
theorem sidon_nonzero_diff_card_le
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (_hSidon : IsSidonInt A) :
    ((DiffFinset A A).erase 0).card ≤ 2 * N - 2 := by
  classical
  let box : Finset ℤ := (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
  have hsub : (DiffFinset A A).erase 0 ⊆ box := by
    intro d hd
    rw [Finset.mem_erase] at hd
    rcases hd with ⟨hd0, hdDiff⟩
    rw [mem_diffFinset] at hdDiff
    rcases hdDiff with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨ha1, haN⟩ := hAint a ha
    obtain ⟨hb1, hbN⟩ := hAint b hb
    change a - b ∈ (Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0
    rw [Finset.mem_erase, Finset.mem_Icc]
    refine ⟨hd0, ?_, ?_⟩ <;> linarith
  refine (Finset.card_le_card hsub).trans ?_
  by_cases hN : N = 0
  · subst N
    simp [box]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have h0 : (0 : ℤ) ∈ Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    have hcard_int :
        ((box.card : ℤ) = (2 * N - 2 : ℕ)) := by
      change
        ((((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).erase 0).card : ℤ) =
          (2 * N - 2 : ℕ))
      rw [Finset.card_erase_of_mem h0]
      have hIcc :
          (((Finset.Icc (1 - (N : ℤ)) ((N : ℤ) - 1)).card : ℤ) =
            2 * (N : ℤ) - 1) := by
        rw [Int.card_Icc_of_le]
        · ring
        · omega
      omega
    exact le_of_eq (Int.ofNat_inj.mp hcard_int)

/-- For `A ⊆ {1, …, N}` Sidon, `binomial(|A|, 2) ≤ N - 1`. Standard counting:
the `binomial(|A|, 2)` positive differences are distinct elements of
`{1, …, N-1}`. -/
theorem sidon_choose_two_le_interval
    (A : Finset ℤ) (N : ℕ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Nat.choose A.card 2 ≤ N - 1 := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hmaps : Set.MapsTo f (A.offDiag : Set (ℤ × ℤ)) ((DiffFinset A A).erase 0 : Set ℤ) := by
    intro ab hab
    have habFin : ab ∈ A.offDiag := by simpa using hab
    rw [Finset.mem_offDiag] at habFin
    rcases habFin with ⟨ha, hb, hne⟩
    change ab.1 - ab.2 ∈ (DiffFinset A A).erase 0
    rw [Finset.mem_erase, mem_diffFinset]
    exact ⟨sub_ne_zero.mpr hne, ⟨ab.1, ha, ab.2, hb, rfl⟩⟩
  have hinj : (A.offDiag : Set (ℤ × ℤ)).InjOn f := by
    intro ab hab cd hcd hdiff
    have habFin : ab ∈ A.offDiag := by simpa using hab
    have hcdFin : cd ∈ A.offDiag := by simpa using hcd
    rw [Finset.mem_offDiag] at habFin hcdFin
    rcases habFin with ⟨hab1, hab2, hab_ne⟩
    rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
    have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by
      dsimp [f] at hdiff
      linarith
    rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
    · exact Prod.ext h.1 h.2.symm
    · exact False.elim (hab_ne h.1)
  have hoff_le :
      A.offDiag.card ≤ ((DiffFinset A A).erase 0).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hordered_le : A.card * A.card - A.card ≤ 2 * N - 2 := by
    rw [← Finset.offDiag_card]
    exact hoff_le.trans (sidon_nonzero_diff_card_le A N hAint hSidon)
  have hdiv :
      (A.card * A.card - A.card) / 2 ≤ (2 * N - 2) / 2 :=
    Nat.div_le_div_right (a := A.card * A.card - A.card) (b := 2 * N - 2) (c := 2)
      hordered_le
  rw [Nat.choose_two_right]
  have hleft : A.card * (A.card - 1) = A.card * A.card - A.card := by
    rw [Nat.mul_sub_one]
  have hright : (2 * N - 2) / 2 = N - 1 := by omega
  simpa [hleft, hright] using hdiv

/-! ## Difference-set helpers -/

lemma diffFinset_erase_zero_card_le_offDiag_card (A : Finset ℤ) :
    ((DiffFinset A A).erase 0).card ≤ A.card * A.card - A.card := by
  classical
  let f : ℤ × ℤ → ℤ := fun ab => ab.1 - ab.2
  have hsub : (DiffFinset A A).erase 0 ⊆ A.offDiag.image f := by
    intro d hd
    rw [Finset.mem_erase, mem_diffFinset] at hd
    rcases hd with ⟨hd0, a, ha, b, hb, rfl⟩
    have hab : a ≠ b := sub_ne_zero.mp hd0
    exact Finset.mem_image.mpr ⟨(a, b), by
      rw [Finset.mem_offDiag]
      exact ⟨ha, hb, hab⟩, rfl⟩
  calc
    ((DiffFinset A A).erase 0).card ≤ (A.offDiag.image f).card := Finset.card_le_card hsub
    _ ≤ A.offDiag.card := Finset.card_image_le
    _ = A.card * A.card - A.card := by rw [Finset.offDiag_card]

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/FiniteFourier.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite-Fourier predicates used by the route.

These predicates use Mathlib's discrete Fourier transform on `ZMod p`. The
transform `ZMod.dft` is unnormalized, so `normalizedDftCoeff` multiplies by
`p⁻¹`, matching the averaged Fourier coefficients in the compact-Cayley and
Fourier-positive notes.

`FourierLowerIndicator` is used by Route A: lower bound `Re ≥ -ε`.
`FourierUpperIndicator` is used by Route B: upper bound `Re ≤ ε` at
nontrivial characters.
-/

namespace Erdos42

open scoped BigOperators ZMod

/-- Complex-valued indicator of a finite set in `ZMod p`. -/
noncomputable def indicatorC {p : ℕ} (T : Finset (ZMod p)) : ZMod p → ℂ :=
  fun x => if x ∈ T then 1 else 0

/-- Normalized DFT coefficient of an arbitrary complex-valued function on
`ZMod p`. This is the common finite-Fourier primitive needed for both assumption
removal projects; `normalizedDftCoeff` is the indicator-specialized version. -/
noncomputable def normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  ((p : ℂ)⁻¹) * (ZMod.dft f r)

/-- Normalized DFT coefficient of the indicator of `T`.

Mathlib's `ZMod.dft` is the counting-measure transform
`∑ x, stdAddChar (-(x * r)) • f x`; the compact-Cayley statements use the
averaged coefficient, hence the factor `(p : ℂ)⁻¹`. -/
noncomputable def normalizedDftCoeff {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) : ℂ :=
  normalizedDftFunction (indicatorC T) r

/-- Normalized Fourier *lower* bound: every character of `ZMod p` evaluated on
`1_F` has real part `≥ -ε`. Used by Route A (Fourier-positive). -/
def FourierLowerIndicator {p : ℕ} [NeZero p] (F : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, -(ε : ℝ) ≤ (normalizedDftCoeff F r).re

/-- Normalized Fourier *upper* bound: every nontrivial character of `ZMod p`
evaluated on `1_T` has real part `≤ ε`. Used by Route B (compact Cayley). -/
def FourierUpperIndicator {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (ε : ℝ) : Prop :=
  ∀ r : ZMod p, r ≠ 0 → (normalizedDftCoeff T r).re ≤ ε

lemma normalizedDftFunction_eq_sum {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction, ZMod.dft_apply]
  simp [smul_eq_mul]

@[simp] lemma normalizedDftFunction_zero_fun {p : ℕ} [NeZero p]
    (r : ZMod p) :
    normalizedDftFunction (fun _ : ZMod p => 0) r = 0 := by
  rw [normalizedDftFunction_eq_sum]
  simp

lemma normalizedDftFunction_add {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x + g x) r =
      normalizedDftFunction f r + normalizedDftFunction g r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum,
    normalizedDftFunction_eq_sum]
  simp [mul_add, Finset.sum_add_distrib]

lemma normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => -f x) r =
      - normalizedDftFunction f r := by
  rw [normalizedDftFunction_eq_sum, normalizedDftFunction_eq_sum]
  simp [Finset.mul_sum]

lemma normalizedDftFunction_sub {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (fun x => f x - g x) r =
      normalizedDftFunction f r - normalizedDftFunction g r := by
  simp [sub_eq_add_neg, normalizedDftFunction_add, normalizedDftFunction_neg]

lemma normalizedDftCoeff_eq_sum {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) (r : ZMod p) :
    normalizedDftCoeff T r =
      ((p : ℂ)⁻¹) * ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [normalizedDftCoeff, normalizedDftFunction_eq_sum]
  simp [indicatorC]

lemma normalizedDftCoeff_zero_eq_card_div {p : ℕ} [NeZero p]
    (T : Finset (ZMod p)) :
    normalizedDftCoeff T 0 = (T.card : ℂ) / (p : ℂ) := by
  rw [normalizedDftCoeff_eq_sum]
  simp [div_eq_inv_mul]

/-- Fourier inversion in the normalized convention, for arbitrary functions. -/
lemma function_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (x : ZMod p) :
    f x =
      ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
  classical
  have h :=
    congrFun (LinearEquiv.symm_apply_apply (ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ))
      f) x
  calc
    f x =
        ((p : ℂ)⁻¹) * ∑ r : ZMod p,
          ZMod.stdAddChar (r * x) * ZMod.dft f r := by
          simpa [ZMod.invDFT_apply, smul_eq_mul] using h.symm
    _ = ∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r := by
          simp [normalizedDftFunction, Finset.mul_sum, mul_comm, mul_left_comm]

lemma sum_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) = 0 := by
  classical
  have hnontrivial :
      AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) ≠ 1 :=
    (ZMod.isPrimitive_stdAddChar p) (by simpa using neg_ne_zero.mpr hr)
  have hsum :
      ∑ x : ZMod p, AddChar.mulShift (ZMod.stdAddChar (N := p)) (-r) x = 0 :=
    AddChar.sum_eq_zero_of_ne_one hnontrivial
  simpa [AddChar.mulShift_apply, mul_comm, mul_left_comm, mul_assoc] using hsum

lemma sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) =
      ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
  classical
  refine Finset.sum_bij (fun x hx => -x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (hT x).mp hx
  · intro x₁ hx₁ x₂ hx₂ h
    exact neg_injective h
  · intro y hy
    refine ⟨-y, ?_, ?_⟩
    · have hy' : - -y ∈ T := by simpa using hy
      exact (hT (-y)).mpr hy'
    · simp
  · intro x hx
    simp

lemma star_sum_stdAddChar_neg_mul_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r))) =
      ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) := by
  classical
  calc
    (starRingEnd ℂ) (∑ x ∈ T, ZMod.stdAddChar (-(x * r)))
        = ∑ x ∈ T, (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) := by
          rw [map_sum]
    _ = ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hchar := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
          simp [hchar] at *
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

lemma star_normalizedDftCoeff_eq_self_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftCoeff T r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum]
  simp [star_sum_stdAddChar_neg_mul_eq_self_of_symmetric hT r]

lemma normalizedDftCoeff_im_eq_zero_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    (normalizedDftCoeff T r).im = 0 := by
  have h := congrArg Complex.im (star_normalizedDftCoeff_eq_self_of_symmetric hT r)
  simp at h
  linarith

lemma normalizedDftCoeff_neg_eq_of_symmetric
    {p : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT : SymmetricFinset T) (r : ZMod p) :
    normalizedDftCoeff T (-r) = normalizedDftCoeff T r := by
  rw [normalizedDftCoeff_eq_sum, normalizedDftCoeff_eq_sum]
  congr 1
  calc
    (∑ x ∈ T, ZMod.stdAddChar (-(x * -r))) =
        ∑ x ∈ T, ZMod.stdAddChar (x * r) := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          congr 1
          ring
    _ = ∑ x ∈ T, ZMod.stdAddChar (-(x * r)) :=
          (sum_stdAddChar_neg_mul_eq_sum_pos_mul_of_symmetric hT r).symm

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/FiniteReduction.lean
    ============================================================= -/

/-
Erdős Problem 42 — shared finite-reduction machinery.

This file contains the route-neutral finite pieces used by both the Fourier-positive Route A and
the compact-Cayley Route B:

  1. Greedy Sidon subset lemma: any sufficiently large finite integer set
     contains a Sidon subset of any prescribed size.
  2. Allowed-difference set: for `A ⊆ [N]` Sidon and prime `p > 2N`, define
     `T_A := (ZMod p) \ ((A − A) ∪ {0})`. Then `T_A` is symmetric, `0 ∉ T_A`,
     `|T_A| ≥ p/2`, and the normalized Fourier transform satisfies an upper
     bound `≤ (|A|−1)/p ≤ ε` for `p` large.
  3. Cyclic-interval averaging: some cyclic interval of length `N` in `ZMod p`
     contains `≥ greedySidonThreshold M` clique elements (uses `p < 8N`).
  4. Lift the clique-in-interval to an integer set `X ⊆ [1, N]` avoiding
     `A − A`; greedily extract a Sidon subset `B ⊆ X` of size `M`.

The Route-specific theorem files import this module; this file imports no analytic
trust-boundary assumption.
-/

namespace Erdos42

open Finset Erdos42

/-! ## Step 1 — greedy Sidon subset bound (compact PDF Lemma 3.2) -/

/-- The compact PDF's greedy Sidon threshold:
`R_M = 1 + (M − 1) + binomial(M−1, 2) + 2 (M − 1) · binomial(M−1, 2)`.

Any finite integer set of size `≥ R_M` contains a Sidon subset of size `M`,
proved by a greedy argument that excludes (a) already-chosen elements, (b)
elements producing an old difference, and (c) midpoints of two chosen
elements. -/
def greedySidonThreshold (M : ℕ) : ℕ :=
  1 + (M - 1) + Nat.choose (M - 1) 2
    + 2 * (M - 1) * Nat.choose (M - 1) 2

/-- The midpoint map on unordered pairs from a finite integer set. -/
noncomputable def midpointMap (B : Finset ℤ) : Sym2 (B : Type) → ℤ :=
  Sym2.lift ⟨fun a b : (B : Type) => (a.1 + b.1) / 2, by
    intro a b
    change (a.1 + b.1) / 2 = (b.1 + a.1) / 2
    rw [add_comm]⟩

/-- Midpoints of distinct unordered pairs from `B`. These are the new values
that would create a collision `x + x = b₁ + b₂`. -/
noncomputable def midpointSet (B : Finset ℤ) : Finset ℤ :=
  ((⊤ : SimpleGraph (B : Type)).edgeFinset).image (midpointMap B)

/-- Values obtained by translating an old nonzero difference by an old point:
these are the new values that can create a one-new-point collision. -/
def shiftedDiffSet (B : Finset ℤ) : Finset ℤ :=
  (B ×ˢ ((DiffFinset B B).erase 0)).image (fun bd => bd.1 + bd.2)

/-- The finite set avoided in the greedy Sidon construction. -/
noncomputable def greedyBadSet (B : Finset ℤ) : Finset ℤ :=
  B ∪ midpointSet B ∪ shiftedDiffSet B

lemma midpointSet_card_le (B : Finset ℤ) :
    (midpointSet B).card ≤ Nat.choose B.card 2 := by
  classical
  calc
    (midpointSet B).card ≤ ((⊤ : SimpleGraph (B : Type)).edgeFinset).card :=
      Finset.card_image_le
    _ = Nat.choose (Fintype.card (B : Type)) 2 :=
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = Nat.choose B.card 2 := by rw [Fintype.card_coe]

lemma mem_midpointSet_of_two_mul_eq {B : Finset ℤ} {x a b : ℤ}
    (ha : a ∈ B) (hb : b ∈ B) (hne : a ≠ b) (hmid : 2 * x = a + b) :
    x ∈ midpointSet B := by
  classical
  let aa : (B : Type) := ⟨a, ha⟩
  let bb : (B : Type) := ⟨b, hb⟩
  have hne' : aa ≠ bb := by
    intro h
    exact hne (Subtype.ext_iff.mp h)
  have hedge : Sym2.mk aa bb ∈ (⊤ : SimpleGraph (B : Type)).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simpa [SimpleGraph.top_adj] using hne'
  refine Finset.mem_image.mpr ⟨Sym2.mk aa bb, hedge, ?_⟩
  change (aa.1 + bb.1) / 2 = x
  have hdvd : (2 : ℤ) ∣ aa.1 + bb.1 := Dvd.intro x (by simpa [aa, bb] using hmid)
  exact (EuclideanDomain.div_eq_iff_eq_mul_of_dvd
      (aa.1 + bb.1) (2 : ℤ) x (by norm_num) hdvd).mpr
    (by simpa [aa, bb] using hmid.symm)

lemma shiftedDiffSet_card_le (B : Finset ℤ) :
    (shiftedDiffSet B).card ≤ B.card * (Nat.choose B.card 2 * 2) := by
  classical
  calc
    (shiftedDiffSet B).card ≤ (B ×ˢ ((DiffFinset B B).erase 0)).card :=
      Finset.card_image_le
    _ = B.card * ((DiffFinset B B).erase 0).card := by rw [Finset.card_product]
    _ ≤ B.card * (B.card * B.card - B.card) := by
      exact Nat.mul_le_mul_left _ (diffFinset_erase_zero_card_le_offDiag_card B)
    _ = B.card * (Nat.choose B.card 2 * 2) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one B.card)]
      rw [Nat.mul_sub_one]

lemma greedyBadSet_card_le (B : Finset ℤ) :
    (greedyBadSet B).card ≤
      B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
  classical
  calc
    (greedyBadSet B).card ≤ B.card + (midpointSet B).card + (shiftedDiffSet B).card := by
      unfold greedyBadSet
      have h₁ :
          (B ∪ midpointSet B ∪ shiftedDiffSet B).card ≤
            (B ∪ midpointSet B).card + (shiftedDiffSet B).card :=
        Finset.card_union_le (B ∪ midpointSet B) (shiftedDiffSet B)
      have h₂ : (B ∪ midpointSet B).card ≤ B.card + (midpointSet B).card :=
        Finset.card_union_le B (midpointSet B)
      omega
    _ ≤ B.card + Nat.choose B.card 2 + B.card * (Nat.choose B.card 2 * 2) := by
      have hmid := midpointSet_card_le B
      have hshift := shiftedDiffSet_card_le B
      omega
    _ = B.card + Nat.choose B.card 2 + 2 * B.card * Nat.choose B.card 2 := by
      ring

lemma greedySidonThreshold_le_succ (M : ℕ) :
    greedySidonThreshold M ≤ greedySidonThreshold (M + 1) := by
  unfold greedySidonThreshold
  have hM : M - 1 ≤ M := Nat.sub_le M 1
  have hchoose : Nat.choose (M - 1) 2 ≤ Nat.choose M 2 :=
    Nat.choose_le_choose 2 hM
  have hprod : (M - 1) * Nat.choose (M - 1) 2 ≤ M * Nat.choose M 2 :=
    Nat.mul_le_mul hM hchoose
  have hlast :
      2 * (M - 1) * Nat.choose (M - 1) 2 ≤ 2 * M * Nat.choose M 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) hchoose
  rw [Nat.add_sub_cancel]
  omega

lemma isSidonInt_insert_of_notMem_greedyBad {B : Finset ℤ} {x : ℤ}
    (hB : IsSidonInt B) (hx : x ∉ greedyBadSet B) :
    IsSidonInt (insert x B) := by
  classical
  rw [greedyBadSet, Finset.mem_union, Finset.mem_union, not_or] at hx
  rcases hx with ⟨hxOldOrMid, hxShift⟩
  rw [not_or] at hxOldOrMid
  rcases hxOldOrMid with ⟨hxB, hxMid⟩
  have no_mid : ∀ {a b : ℤ}, a ∈ B → b ∈ B → a ≠ b → 2 * x ≠ a + b := by
    intro a b ha hb hne h
    exact hxMid (mem_midpointSet_of_two_mul_eq ha hb hne h)
  have no_shift :
      ∀ {c d : ℤ}, c ∈ B → d ∈ (DiffFinset B B).erase 0 → c + d ≠ x := by
    intro c d hc hd h
    apply hxShift
    exact Finset.mem_image.mpr ⟨(c, d), by
      rw [Finset.mem_product]
      exact ⟨hc, hd⟩, h⟩
  intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
  rw [Finset.mem_insert] at ha₁ ha₂ ha₃ ha₄
  rcases ha₁ with h₁ | ha₁
  · subst a₁
    rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exact Or.inl ⟨rfl, rfl⟩
        · exfalso
          have hx4 : x = a₄ := by linarith
          exact hxB (by simpa [hx4] using ha₄)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx3 : x = a₃ := by linarith
          exact hxB (by simpa [hx3] using ha₃)
        · exfalso
          by_cases h34 : a₃ = a₄
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · exact no_mid ha₃ ha₄ h34 (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx2 : x = a₂ := by linarith
          exact hxB (by simpa [hx2] using ha₂)
        · have h24 : a₂ = a₄ := by linarith
          exact Or.inl ⟨rfl, h24⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h23 : a₂ = a₃ := by linarith
          exact Or.inr ⟨rfl, h23⟩
        · exfalso
          by_cases h42 : a₄ = a₂
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₂ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h42, ⟨a₄, ha₄, a₂, ha₂, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
  · rcases ha₂ with h₂ | ha₂
    · subst a₂
      rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          have hx1 : x = a₁ := by linarith
          exact hxB (by simpa [hx1] using ha₁)
        · have h14 : a₁ = a₄ := by linarith
          exact Or.inr ⟨h14, rfl⟩
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          have h13 : a₁ = a₃ := by linarith
          exact Or.inl ⟨h13, rfl⟩
        · exfalso
          by_cases h41 : a₄ = a₁
          · subst a₄
            have hx3 : x = a₃ := by linarith
            exact hxB (by simpa [hx3] using ha₃)
          · have hd : a₄ - a₁ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h41, ⟨a₄, ha₄, a₁, ha₁, rfl⟩⟩
            exact no_shift ha₃ hd (by linarith)
    · rcases ha₃ with h₃ | ha₃
      · subst a₃
        rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h12 : a₁ = a₂
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · exact no_mid ha₁ ha₂ h12 (by linarith)
        · exfalso
          by_cases h24 : a₂ = a₄
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₄ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h24, ⟨a₂, ha₂, a₄, ha₄, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
      · rcases ha₄ with h₄ | ha₄
        · subst a₄
          exfalso
          by_cases h23 : a₂ = a₃
          · subst a₂
            have hx1 : x = a₁ := by linarith
            exact hxB (by simpa [hx1] using ha₁)
          · have hd : a₂ - a₃ ∈ (DiffFinset B B).erase 0 := by
              rw [Finset.mem_erase, mem_diffFinset]
              exact ⟨sub_ne_zero.mpr h23, ⟨a₂, ha₂, a₃, ha₃, rfl⟩⟩
            exact no_shift ha₁ hd (by linarith)
        · exact hB ha₁ ha₂ ha₃ ha₄ hsum

/-- Greedy Sidon subset bound: every large integer `Finset` contains a Sidon
subset of any prescribed size. -/
theorem exists_sidon_subset_of_card_ge
    (M : ℕ) (X : Finset ℤ)
    (hX : greedySidonThreshold M ≤ X.card) :
    ∃ B : Finset ℤ, B ⊆ X ∧ B.card = M ∧ IsSidonInt B := by
  classical
  induction M with
  | zero =>
      exact ⟨∅, by simp, by simp, isSidonInt_empty⟩
  | succ M ih =>
      have hXM : greedySidonThreshold M ≤ X.card :=
        (greedySidonThreshold_le_succ M).trans hX
      obtain ⟨B, hBX, hBcard, hBsidon⟩ := ih hXM
      have hbad_lt : (greedyBadSet B).card < X.card := by
        have hbad_le := greedyBadSet_card_le B
        have hbad_leM :
            (greedyBadSet B).card ≤
              M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          simpa [hBcard] using hbad_le
        have hthresh :
            greedySidonThreshold (M + 1) =
              1 + M + Nat.choose M 2 + 2 * M * Nat.choose M 2 := by
          unfold greedySidonThreshold
          rw [Nat.add_sub_cancel]
        have hbad_lt_threshold : (greedyBadSet B).card < greedySidonThreshold (M + 1) := by
          rw [hthresh]
          omega
        exact hbad_lt_threshold.trans_le hX
      obtain ⟨x, hxX, hxBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt
      have hxB : x ∉ B := by
        intro hxB
        apply hxBad
        unfold greedyBadSet
        simp [hxB]
      refine ⟨insert x B, ?_, ?_, ?_⟩
      · intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxX
        · exact hBX hy
      · rw [Finset.card_insert_of_notMem hxB, hBcard]
      · exact isSidonInt_insert_of_notMem_greedyBad hBsidon hxBad

/-! ## Step 2 — allowed-difference set & Fourier upper bound -/

/-- The allowed-difference set: `T_A := (ZMod p) \ ((A − A) ∪ {0})` viewed
through the natural cast `ℤ → ZMod p`. -/
noncomputable def allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  (Finset.univ : Finset (ZMod p)).filter
    (fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t)

/-- The allowed-difference set is symmetric. -/
lemma allowedDiffSetMod_symmetric (p : ℕ) [NeZero p] (A : Finset ℤ) :
    SymmetricFinset (allowedDiffSetMod p A) := by
  intro t
  simp only [allowedDiffSetMod, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = t := by simp [hdiff]
      exact ht b hb a ha hswap
  · rintro ⟨ht0, ht⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      exact ht0 (by simpa using congrArg Neg.neg hzero)
    · intro a ha b hb hdiff
      have hswap : ((b - a : ℤ) : ZMod p) = -t := by
        calc
          ((b - a : ℤ) : ZMod p) = -(((a - b : ℤ) : ZMod p)) := by norm_num
          _ = -t := by simp [hdiff]
      exact ht b hb a ha hswap

/-- `0` is not in the allowed-difference set (by construction). -/
lemma zero_notMem_allowedDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    (0 : ZMod p) ∉ allowedDiffSetMod p A := by
  simp [allowedDiffSetMod]

/-- Density bound: for `A ⊆ [N]` Sidon and `p > 4N`, the allowed-difference
set covers more than half of `ZMod p`. -/
lemma allowedDiffSetMod_density
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    (1 / 2 : ℝ) * p ≤ ((allowedDiffSetMod p A).card : ℝ) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hAempty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have ha' := hAint a ha
      omega
    have hcard : (allowedDiffSetMod p A).card = p - 1 := by
      have hallowed_eq :
          allowedDiffSetMod p A = (Finset.univ : Finset (ZMod p)).erase 0 := by
        ext t
        simp [allowedDiffSetMod, hAempty]
      rw [hallowed_eq, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
        Finset.card_univ, ZMod.card]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    rw [hcard]
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp2
    nlinarith
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let P : ZMod p → Prop :=
      fun t => t ≠ 0 ∧ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t
    let bad : Finset (ZMod p) := (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)
    let forbidden : Finset (ZMod p) :=
      insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
    have hbad_subset : bad ⊆ forbidden := by
      intro t ht
      change t ∈ (Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t) at ht
      rw [Finset.mem_filter] at ht
      rcases ht with ⟨_htuniv, htbad⟩
      by_cases ht0 : t = 0
      · change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        simp [ht0]
      · have hnot :
            ¬ ∀ a ∈ A, ∀ b ∈ A, ((a - b : ℤ) : ZMod p) ≠ t := by
          intro hall
          exact htbad ⟨ht0, hall⟩
        push Not at hnot
        rcases hnot with ⟨a, ha, b, hb, hcast⟩
        have hdiff_ne : a - b ≠ 0 := by
          intro hzero
          apply ht0
          simpa [hzero] using hcast.symm
        have hdiff_mem : a - b ∈ (DiffFinset A A).erase 0 := by
          rw [Finset.mem_erase, mem_diffFinset]
          exact ⟨hdiff_ne, ⟨a, ha, b, hb, rfl⟩⟩
        change t ∈ insert 0 (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p)))
        exact Finset.mem_insert.mpr
          (Or.inr (Finset.mem_image.mpr ⟨a - b, hdiff_mem, hcast⟩))
    have hbad_card : bad.card ≤ 2 * N - 1 := by
      calc
        bad.card ≤ forbidden.card := Finset.card_le_card hbad_subset
        _ ≤ (((DiffFinset A A).erase 0).image (fun x : ℤ => (x : ZMod p))).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ ((DiffFinset A A).erase 0).card + 1 :=
          Nat.add_le_add_right Finset.card_image_le 1
        _ ≤ (2 * N - 2) + 1 :=
          Nat.add_le_add_right (sidon_nonzero_diff_card_le A N hAint hSidon) 1
        _ ≤ 2 * N - 1 := by omega
    have hsum : (allowedDiffSetMod p A).card + bad.card = p := by
      change
        ((Finset.univ : Finset (ZMod p)).filter P).card +
            ((Finset.univ : Finset (ZMod p)).filter (fun t => ¬ P t)).card = p
      rw [Finset.card_filter_add_card_filter_not]
      simp [ZMod.card]
    have hbad_half : 2 * bad.card ≤ p := by omega
    have hallowed_nat : p ≤ 2 * (allowedDiffSetMod p A).card := by omega
    have hallowed_real :
        (p : ℝ) ≤ 2 * ((allowedDiffSetMod p A).card : ℝ) := by
      exact_mod_cast hallowed_nat
    nlinarith

lemma int_difference_eq_of_zmod_eq_of_interval
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    {a b c d : ℤ}
    (ha : 1 ≤ a ∧ a ≤ (N : ℤ))
    (hb : 1 ≤ b ∧ b ≤ (N : ℤ))
    (hc : 1 ≤ c ∧ c ≤ (N : ℤ))
    (hd : 1 ≤ d ∧ d ≤ (N : ℤ))
    (hcong : ((a - b : ℤ) : ZMod p) = ((c - d : ℤ) : ZMod p)) :
    a - b = c - d := by
  have hdiv : (p : ℤ) ∣ (c - d) - (a - b) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a - b) (c - d) p).mp hcong
  have hp_bound : (2 * (N : ℤ) : ℤ) < (p : ℤ) := by exact_mod_cast (by omega)
  have habs : |(c - d) - (a - b)| < (p : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hzero : (c - d) - (a - b) = 0 := Int.eq_zero_of_abs_lt_dvd hdiv habs
  linarith

lemma offDiag_diff_cast_injOn
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A) :
    Set.InjOn (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))
      (A.offDiag : Set (ℤ × ℤ)) := by
  intro ab hab cd hcd hcast
  have habFin : ab ∈ A.offDiag := by simpa using hab
  have hcdFin : cd ∈ A.offDiag := by simpa using hcd
  rw [Finset.mem_offDiag] at habFin hcdFin
  rcases habFin with ⟨hab1, hab2, hab_ne⟩
  rcases hcdFin with ⟨hcd1, hcd2, _hcd_ne⟩
  have hdiff : ab.1 - ab.2 = cd.1 - cd.2 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 hab1) (hAint ab.2 hab2) (hAint cd.1 hcd1) (hAint cd.2 hcd2) hcast
  have hsum : ab.1 + cd.2 = cd.1 + ab.2 := by linarith
  rcases hSidon hab1 hcd2 hcd1 hab2 hsum with h | h
  · exact Prod.ext h.1 h.2.symm
  · exact False.elim (hab_ne h.1)

/-- Nonzero ordered difference residues from `A`. -/
noncomputable def offDiagDiffSetMod (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Finset (ZMod p) :=
  A.offDiag.image (fun ab : ℤ × ℤ => ((ab.1 - ab.2 : ℤ) : ZMod p))

lemma zero_notMem_offDiagDiffSetMod
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) :
    (0 : ZMod p) ∉ offDiagDiffSetMod p A := by
  classical
  rw [offDiagDiffSetMod, Finset.mem_image]
  rintro ⟨ab, hab, hcast⟩
  rw [Finset.mem_offDiag] at hab
  rcases hab with ⟨ha, hb, hne⟩
  have hcong :
      ((ab.1 - ab.2 : ℤ) : ZMod p) = ((ab.1 - ab.1 : ℤ) : ZMod p) := by
    simpa using hcast
  have hdiff :
      ab.1 - ab.2 = ab.1 - ab.1 :=
    int_difference_eq_of_zmod_eq_of_interval (p := p) (N := N) hbig
      (hAint ab.1 ha) (hAint ab.2 hb) (hAint ab.1 ha) (hAint ab.1 ha) hcong
  exact hne (by linarith)

lemma allowedDiffSetMod_union_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A) =
      (Finset.univ : Finset (ZMod p)) := by
  classical
  ext t
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_univ, iff_true]
  by_cases ht_allowed : t ∈ allowedDiffSetMod p A
  · exact Or.inl ht_allowed
  · right
    rw [allowedDiffSetMod, Finset.mem_filter] at ht_allowed
    simp only [Finset.mem_univ, true_and, not_and, not_forall] at ht_allowed
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    · right
      have hnot_all := ht_allowed ht0
      push Not at hnot_all
      rcases hnot_all with ⟨a, ha, b, hb, hdiff⟩
      rw [offDiagDiffSetMod, Finset.mem_image]
      by_cases hab : a = b
      · subst b
        exfalso
        exact ht0 (by simpa using hdiff.symm)
      · refine ⟨(a, b), ?_, hdiff⟩
        rw [Finset.mem_offDiag]
        exact ⟨ha, hb, hab⟩

lemma disjoint_allowedDiffSetMod_forbidden (p : ℕ) [NeZero p] (A : Finset ℤ) :
    Disjoint (allowedDiffSetMod p A) (insert 0 (offDiagDiffSetMod p A)) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht hforbidden
  rw [allowedDiffSetMod, Finset.mem_filter] at ht
  rcases ht with ⟨_htuniv, ht0, hno⟩
  rw [Finset.mem_insert] at hforbidden
  rcases hforbidden with rfl | hoff
  · exact ht0 rfl
  · rw [offDiagDiffSetMod, Finset.mem_image] at hoff
    rcases hoff with ⟨ab, hab, hdiff⟩
    rw [Finset.mem_offDiag] at hab
    rcases hab with ⟨ha, hb, _hne⟩
    exact hno ab.1 ha ab.2 hb hdiff

lemma sum_allowedDiffSetMod_eq_neg_forbidden
    {p : ℕ} [Fact p.Prime] [NeZero p]
    (A : Finset ℤ) {r : ZMod p} (hr : r ≠ 0) :
    ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      - ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
  classical
  have htotal := sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) hr
  have hsum_union :
      ∑ x ∈ allowedDiffSetMod p A ∪ insert 0 (offDiagDiffSetMod p A),
          ZMod.stdAddChar (-(x * r)) =
        ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) := by
    rw [Finset.sum_union (disjoint_allowedDiffSetMod_forbidden p A)]
  rw [allowedDiffSetMod_union_forbidden p A] at hsum_union
  have hadd :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) +
          ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) = 0 := by
    rw [← hsum_union]
    exact htotal
  exact eq_neg_of_add_eq_zero_left hadd

lemma sum_forbidden_eq_one_add_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (r : ZMod p) :
    ∑ x ∈ insert 0 (offDiagDiffSetMod p A), ZMod.stdAddChar (-(x * r)) =
      1 + ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) := by
  classical
  rw [Finset.sum_insert (zero_notMem_offDiagDiffSetMod (p := p) (N := N) hbig A hAint)]
  simp

lemma sum_offDiagDiffSetMod_eq_sum_offDiag
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (f : ZMod p → ℂ) :
    ∑ x ∈ offDiagDiffSetMod p A, f x =
      ∑ ab ∈ A.offDiag, f (((ab.1 - ab.2 : ℤ) : ZMod p)) := by
  classical
  rw [offDiagDiffSetMod]
  rw [Finset.sum_image]
  intro ab hab cd hcd h
  exact offDiag_diff_cast_injOn (p := p) (N := N) hbig A hAint hSidon
    (by simpa using hab) (by simpa using hcd) h

lemma sum_product_eq_sum_diag_add_sum_offDiag
    (A : Finset ℤ) (f : ℤ × ℤ → ℂ) :
    ∑ ab ∈ A ×ˢ A, f ab =
      (∑ a ∈ A, f (a, a)) + ∑ ab ∈ A.offDiag, f ab := by
  classical
  rw [← Finset.diag_union_offDiag (s := A)]
  rw [Finset.sum_union (Finset.disjoint_diag_offDiag A)]
  rw [Finset.sum_diag]

lemma sum_product_stdAddChar_neg_diff
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    (∑ ab ∈ A ×ˢ A,
        ZMod.stdAddChar (-(((ab.1 - ab.2 : ℤ) : ZMod p) * r))) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) := by
  classical
  rw [Finset.sum_product]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  refine Finset.sum_congr rfl ?_
  intro b hb
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  norm_num
  ring_nf

lemma sum_offDiagDiffSetMod_stdAddChar_eq
    {p N : ℕ} [NeZero p] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (r : ZMod p) :
    ∑ x ∈ offDiagDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))) - (A.card : ℂ) := by
  classical
  let F : ℤ × ℤ → ℂ :=
    fun ab => ZMod.stdAddChar (-((((ab.1 - ab.2 : ℤ) : ZMod p) * r)))
  have hoff :=
    sum_offDiagDiffSetMod_eq_sum_offDiag (p := p) (N := N) hbig A hAint hSidon
      (fun x : ZMod p => ZMod.stdAddChar (-(x * r)))
  have hsplit := sum_product_eq_sum_diag_add_sum_offDiag A F
  have hprod := sum_product_stdAddChar_neg_diff A r
  have hdiag : ∑ a ∈ A, F (a, a) = (A.card : ℂ) := by
    simp [F]
  rw [hoff]
  have hsplit' :
      ∑ ab ∈ A.offDiag, F ab =
        (∑ ab ∈ A ×ˢ A, F ab) - ∑ a ∈ A, F (a, a) := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hsplit.symm
  rw [hprod] at hsplit'
  simpa [F, hdiag] using hsplit'

lemma stdAddChar_neg_eq_conj {p : ℕ} [NeZero p] (x : ZMod p) :
    ZMod.stdAddChar (-x) = (starRingEnd ℂ) (ZMod.stdAddChar x) := by
  simpa using AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) x

lemma sum_stdAddChar_neg_eq_conj_sum
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
      (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
  classical
  calc
    ∑ b ∈ A, ZMod.stdAddChar (-(((b : ZMod p) * r))) =
        ∑ a ∈ A, (starRingEnd ℂ) (ZMod.stdAddChar (((a : ZMod p) * r))) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact stdAddChar_neg_eq_conj (p := p) (((a : ZMod p) * r))
    _ = (starRingEnd ℂ) (∑ a ∈ A, ZMod.stdAddChar (((a : ZMod p) * r))) := by
      simp

lemma stdAddChar_neg_product_re_nonneg
    {p : ℕ} [NeZero p] (A : Finset ℤ) (r : ZMod p) :
    0 ≤
      ((∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
        (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))).re := by
  classical
  let S : ℂ := ∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r))
  have hneg :
      (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) =
        (starRingEnd ℂ) S := by
    simpa [S] using sum_stdAddChar_neg_eq_conj_sum A r
  rw [hneg]
  rw [← Complex.normSq_eq_conj_mul_self]
  simpa using Complex.normSq_nonneg S

lemma sum_allowedDiffSetMod_stdAddChar_re_le
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    {r : ZMod p} (hr : r ≠ 0) :
    (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
      ((A.card - 1 : ℕ) : ℝ) := by
  classical
  let P : ℂ :=
    (∑ a ∈ A, ZMod.stdAddChar (-(((a : ZMod p) * r)))) *
      (∑ b ∈ A, ZMod.stdAddChar (((b : ZMod p) * r)))
  have hallowed :=
    sum_allowedDiffSetMod_eq_neg_forbidden (p := p) A hr
  have hforbidden :=
    sum_forbidden_eq_one_add_offDiag (p := p) (N := N) hbig A hAint r
  have hoff :=
    sum_offDiagDiffSetMod_stdAddChar_eq (p := p) (N := N) hbig A hAint hSidon r
  have hsum :
      ∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r)) =
        (A.card : ℂ) - 1 - P := by
    rw [hallowed, hforbidden, hoff]
    simp [P]
    ring
  have hP_nonneg : 0 ≤ P.re := by
    simpa [P] using stdAddChar_neg_product_re_nonneg A r
  rw [hsum]
  by_cases hA0 : A.card = 0
  · simp [hA0]
    linarith
  · have hApos : 1 ≤ A.card := by omega
    have hcast : ((A.card - 1 : ℕ) : ℝ) = (A.card : ℝ) - 1 := by
      rw [Nat.cast_sub hApos]
      norm_num
    rw [hcast]
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, tsub_le_iff_right,
      le_add_iff_nonneg_right, ge_iff_le]
    exact hP_nonneg

/-- Sidon Fourier estimate (normalized): `Re 1̂_{T_A}(r) ≤ (|A|−1)/p` for every
nontrivial character `r`, for `T_A = (ZMod p) \ ((A−A) ∪ {0})` and `A` Sidon
(compact PDF §3 calculation).

This is a finite Fourier calculation, separate from the compact-Cayley clique
theorem. It expands `ZMod.dft`, uses the vanishing of nontrivial character sums,
and rewrites the nonzero-difference contribution as
`|∑ a ∈ A, χ a|^2 - |A|`. -/
theorem allowedDiffs_fourier_upper
    {p N : ℕ} [Fact p.Prime] (hbig : 4 * N < p)
    (A : Finset ℤ)
    (hAint : ∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ))
    (hSidon : IsSidonInt A)
    (ε : ℝ)
    (hε : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε) :
    FourierUpperIndicator (allowedDiffSetMod p A) ε := by
  classical
  intro r hr
  have hp_pos_nat : 0 < p := (Fact.out : p.Prime).pos
  have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos_nat
  have hsum_le :=
    sum_allowedDiffSetMod_stdAddChar_re_le (p := p) (N := N) hbig A hAint hSidon hr
  rw [normalizedDftCoeff_eq_sum]
  have hinv : ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hinv, Complex.re_ofReal_mul]
  have hmul_le :
      (p : ℝ)⁻¹ *
          (∑ x ∈ allowedDiffSetMod p A, ZMod.stdAddChar (-(x * r))).re ≤
        (p : ℝ)⁻¹ * ((A.card - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hp_pos.le)
  refine hmul_le.trans ?_
  rw [div_eq_inv_mul] at hε
  simpa [mul_comm] using hε

/-- Eventual smallness of the normalized Sidon-size error term.

For `A ⊆ [1,N]` Sidon, `choose |A| 2 ≤ N - 1`, so `|A| = O(sqrt N)`.
Since the chosen prime satisfies `p > 4N`, `( |A| - 1 ) / p → 0`. This
elementary asymptotic bound is kept separate from the finite Fourier identity
above. -/
lemma sidon_card_minus_one_div_prime_eventually_small
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Nε : ℕ, ∀ N p : ℕ,
      Nε ≤ N →
      4 * N < p →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) →
        IsSidonInt A →
        ((A.card - 1 : ℕ) : ℝ) / p ≤ ε := by
  classical
  have hden_pos : 0 < 8 * ε ^ 2 := by positivity
  obtain ⟨Nε, hNε_gt⟩ := exists_nat_gt ((1 : ℝ) / (8 * ε ^ 2))
  refine ⟨Nε, ?_⟩
  intro N p hN hp A hAint hSidon
  let t : ℝ := ((A.card - 1 : ℕ) : ℝ)
  let k : ℝ := (A.card : ℝ)
  have hN_large_base : (1 : ℝ) / (8 * ε ^ 2) < (N : ℝ) :=
    hNε_gt.trans_le (by exact_mod_cast hN)
  have hN_large : 1 < 8 * ε ^ 2 * (N : ℝ) := by
    have := (div_lt_iff₀ hden_pos).mp hN_large_base
    nlinarith
  have hN_pos : 0 < (N : ℝ) := (one_div_pos.mpr hden_pos).trans hN_large_base
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hp_gt4N : 4 * (N : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hchoose := sidon_choose_two_le_interval A N hAint hSidon
  by_cases hAcard0 : A.card = 0
  · simp [hAcard0, le_of_lt hε]
  have hAcard_pos : 1 ≤ A.card := by omega
  have ht_eq : t = (A.card : ℝ) - 1 := by
    dsimp [t]
    rw [Nat.cast_sub hAcard_pos]
    norm_num
  have hchoose_real :
      (Nat.choose A.card 2 : ℝ) ≤ (N - 1 : ℕ) := by exact_mod_cast hchoose
  have hchoose_le_N :
      k * t / 2 ≤ (N : ℝ) := by
    have hformula :
        (Nat.choose A.card 2 : ℝ) = k * t / 2 := by
      simpa [k, ht_eq] using (Nat.cast_choose_two (K := ℝ) A.card)
    have hsub_le : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.sub_le N 1)
    nlinarith
  have ht_nonneg : 0 ≤ t := by positivity
  have hk_nonneg : 0 ≤ k := by positivity
  have ht_le_k : t ≤ k := by
    dsimp [t, k]
    exact_mod_cast (Nat.sub_le A.card 1)
  have ht_sq_le : t ^ 2 ≤ 2 * (N : ℝ) := by
    have hsq_le : t * t ≤ k * t := by nlinarith
    nlinarith
  have htarget_sq : t ^ 2 ≤ (ε * (p : ℝ)) ^ 2 := by
    have hεsq_pos : 0 < ε ^ 2 := by positivity
    have hp_sq_gt : (4 * (N : ℝ)) ^ 2 < (p : ℝ) ^ 2 := by
      nlinarith [hp_gt4N, hN_pos, hp_pos, sq_nonneg ((p : ℝ) - 4 * (N : ℝ))]
    nlinarith
  have ht_le_epsp : t ≤ ε * (p : ℝ) := by
    exact le_of_sq_le_sq htarget_sq (by positivity)
  rw [div_le_iff₀ hp_pos]
  simpa [t] using ht_le_epsp

/-! ## Step 3 — cyclic interval averaging -/

/-- Cyclic interval `{s, s+1, …, s+N-1}` in `ZMod p`. -/
noncomputable def cyclicInterval (p N : ℕ) [NeZero p] (s : ZMod p) :
    Finset (ZMod p) :=
  (Finset.range N).image (fun i : ℕ => s + (i : ZMod p))

lemma nat_eq_of_zmod_eq_of_lt {p i j : ℕ} [NeZero p]
    (hi : i < p) (hj : j < p) (hij : (i : ZMod p) = (j : ZMod p)) :
    i = j := by
  have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' i j p).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hmod
  exact hmod

/-- Integer lift of clique points lying in the cyclic interval
`{s, …, s+N-1}`. The residue `s+i` is lifted to the integer `i+1`, so the
lift lies in `[1, N]`. -/
noncomputable def intervalLiftSet (p N : ℕ) [NeZero p] (s : ZMod p)
    (C : Finset (ZMod p)) : Finset ℤ :=
  ((Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)).image
    (fun i : ℕ => (i + 1 : ℤ))

lemma intervalLiftSet_card_eq
    {p N : ℕ} [NeZero p] (hpN : N < p) (s : ZMod p) (C : Finset (ZMod p)) :
    (intervalLiftSet p N s C).card =
      (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  let I : Finset ℕ := (Finset.range N).filter (fun i : ℕ => s + (i : ZMod p) ∈ C)
  let f : ℕ → ZMod p := fun i => s + (i : ZMod p)
  let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
  have hinjI : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj hij
    have hiI : i ∈ I := by simpa using hi
    have hjI : j ∈ I := by simpa using hj
    rw [Finset.mem_filter] at hiI hjI
    apply nat_eq_of_zmod_eq_of_lt
      (Nat.lt_trans (by simpa using hiI.1) hpN)
      (Nat.lt_trans (by simpa using hjI.1) hpN)
    apply add_left_cancel (a := s)
    simpa [f] using hij
  have hI_image_card : (I.image f).card = I.card :=
    Finset.card_image_of_injOn hinjI
  have hI_image : I.image f = target := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨i, hiI, rfl⟩
      rw [Finset.mem_filter] at hiI
      rw [Finset.mem_filter]
      refine ⟨hiI.2, ?_⟩
      rw [cyclicInterval]
      exact Finset.mem_image.mpr ⟨i, hiI.1, rfl⟩
    · intro hx
      change x ∈ target at hx
      rw [Finset.mem_filter] at hx
      rcases hx with ⟨hxC, hxInt⟩
      rw [cyclicInterval, Finset.mem_image] at hxInt
      rcases hxInt with ⟨i, hiN, rfl⟩
      rw [Finset.mem_image]
      exact ⟨i, by
        rw [Finset.mem_filter]
        exact ⟨hiN, hxC⟩, rfl⟩
  have hlift_card : (intervalLiftSet p N s C).card = I.card := by
    unfold intervalLiftSet
    change (I.image (fun i : ℕ => (i + 1 : ℤ))).card = I.card
    apply Finset.card_image_of_injOn
    intro i _hi j _hj hij
    have hnat : i + 1 = j + 1 := Int.ofNat_inj.mp hij
    omega
  calc
    (intervalLiftSet p N s C).card = I.card := hlift_card
    _ = (I.image f).card := hI_image_card.symm
    _ = target.card := by rw [hI_image]

lemma mem_intervalLiftSet.mp
    {p N : ℕ} [NeZero p] {s : ZMod p} {C : Finset (ZMod p)} {b : ℤ}
    (hb : b ∈ intervalLiftSet p N s C) :
    ∃ i : ℕ, i < N ∧ s + (i : ZMod p) ∈ C ∧ b = (i + 1 : ℤ) := by
  classical
  rw [intervalLiftSet, Finset.mem_image] at hb
  rcases hb with ⟨i, hi, rfl⟩
  rw [Finset.mem_filter] at hi
  exact ⟨i, by simpa using hi.1, hi.2, rfl⟩

/-- Pigeonhole: a clique of size `8R` in `ZMod p` (with `p < 8N`) intersects
some cyclic interval of length `N` in at least `R` points. -/
theorem exists_large_intersection_cyclicInterval
    {p N R : ℕ} [NeZero p] (hpN : N < p) (C : Finset (ZMod p))
    (hsize : C.card = 8 * R)
    (hpupper : p < 8 * N) :
    ∃ s : ZMod p,
      R ≤ (C.filter (fun x => x ∈ cyclicInterval p N s)).card := by
  classical
  by_cases hR0 : R = 0
  · subst R
    exact ⟨0, by simp⟩
  · have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
    let D : Finset (ZMod p × ℕ) := C.product (Finset.range N)
    let start : ZMod p × ℕ → ZMod p := fun ci => ci.1 - (ci.2 : ZMod p)
    have hlarge :
        (Finset.univ : Finset (ZMod p)).card * R < D.card := by
      rw [Finset.card_univ, ZMod.card]
      change p * R < (C ×ˢ Finset.range N).card
      rw [Finset.card_product, Finset.card_range, hsize]
      calc
        p * R < (8 * N) * R := Nat.mul_lt_mul_of_pos_right hpupper hRpos
        _ = (8 * R) * N := by ring
    obtain ⟨s, _hsuniv, hs⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := D) (t := (Finset.univ : Finset (ZMod p))) (f := start) (n := R)
        (by intro x _hx; exact Finset.mem_univ _) hlarge
    refine ⟨s, ?_⟩
    let fiber : Finset (ZMod p × ℕ) := D.filter (fun ci => start ci = s)
    let target : Finset (ZMod p) := C.filter (fun x => x ∈ cyclicInterval p N s)
    have hmaps :
        Set.MapsTo (fun ci : ZMod p × ℕ => ci.1)
          (fiber : Set (ZMod p × ℕ)) (target : Set (ZMod p)) := by
      intro ci hci
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      rw [Finset.mem_filter] at hci'
      rcases hci' with ⟨hciD, hstart⟩
      have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
        simpa [D] using hciD
      rcases hmem with ⟨hc, hi⟩
      have hpoint : ci.1 ∈ cyclicInterval p N s := by
        rw [cyclicInterval]
        refine Finset.mem_image.mpr ⟨ci.2, hi, ?_⟩
        have hadd : ci.1 = s + (ci.2 : ZMod p) := by
          simpa [start] using (sub_eq_iff_eq_add.mp hstart)
        exact hadd.symm
      change ci.1 ∈ C.filter (fun x => x ∈ cyclicInterval p N s)
      rw [Finset.mem_filter]
      exact ⟨hc, hpoint⟩
    have hinj :
        (fiber : Set (ZMod p × ℕ)).InjOn (fun ci : ZMod p × ℕ => ci.1) := by
      intro ci hci cj hcj hproj
      have hci' : ci ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hci
      have hcj' : cj ∈ D.filter (fun ci => start ci = s) := by
        simpa [fiber] using hcj
      rw [Finset.mem_filter] at hci' hcj'
      rcases hci' with ⟨hciD, hstart_i⟩
      rcases hcj' with ⟨hcjD, hstart_j⟩
      have hi : ci.2 ∈ Finset.range N := by
        have hmem : ci.1 ∈ C ∧ ci.2 ∈ Finset.range N := by
          simpa [D] using hciD
        exact hmem.2
      have hj : cj.2 ∈ Finset.range N := by
        have hmem : cj.1 ∈ C ∧ cj.2 ∈ Finset.range N := by
          simpa [D] using hcjD
        exact hmem.2
      have hci_add : ci.1 = s + (ci.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_i)
      have hcj_add : cj.1 = s + (cj.2 : ZMod p) := by
        simpa [start] using (sub_eq_iff_eq_add.mp hstart_j)
      have hcast : (ci.2 : ZMod p) = (cj.2 : ZMod p) := by
        apply add_left_cancel (a := s)
        calc
          s + (ci.2 : ZMod p) = ci.1 := hci_add.symm
          _ = cj.1 := hproj
          _ = s + (cj.2 : ZMod p) := hcj_add
      have hmod : ci.2 % p = cj.2 % p := by
        exact (ZMod.natCast_eq_natCast_iff' ci.2 cj.2 p).mp hcast
      have hilt : ci.2 < p := by
        exact Nat.lt_trans (by simpa using hi) hpN
      have hjlt : cj.2 < p := by
        exact Nat.lt_trans (by simpa using hj) hpN
      have hidx : ci.2 = cj.2 := by
        rw [Nat.mod_eq_of_lt hilt, Nat.mod_eq_of_lt hjlt] at hmod
        exact hmod
      exact Prod.ext hproj hidx
    have hfiber_le : fiber.card ≤ target.card :=
      Finset.card_le_card_of_injOn (fun ci : ZMod p × ℕ => ci.1) hmaps hinj
    have hs' : R < fiber.card := by
      simpa [fiber] using hs
    exact (Nat.le_of_lt hs').trans hfiber_le

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Counterexample.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley counterexample sequence.

This is the Route B contradiction skeleton for opening
`compact_cayley_clique`.  It is independent of Route A: if the explicit-prime
compact Cayley statement fails, then one can choose primes `p_n → ∞` and
allowed sets `T_n ⊆ ZMod p_n` with density `η`, zero-free symmetry, Fourier
upper bias tending to zero, and no `K_ℓ` clique.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

/-- Explicit-prime version of the compact Cayley theorem statement.  This
avoids typeclass binders in the counterexample extraction; it is equivalent in
content to the Route B trust-boundary assumption's statement. -/
def CompactCayleyCliqueStatementExplicit (ℓ : ℕ) (η : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
  ∃ p₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      (letI : NeZero p := ⟨hp.ne_zero⟩; FourierUpperIndicator T ε) →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C

/-- The explicit-prime compact-Cayley statement implies the original
typeclass-shaped statement used by the Route B trust-boundary assumption. -/
theorem compactCayleyCliqueStatement_from_explicit
    {ℓ : ℕ} {η : ℝ}
    (h : CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨ε, hε, p₀, hp₀⟩
  refine ⟨ε, hε, p₀, ?_⟩
  intro p hpFact hpgt T hsym hzero hdens hfourier
  have hp : p.Prime := Fact.out
  exact hp₀ p hp hpgt T hsym hzero hdens (by simpa using hfourier)

/-- A sequence of finite Cayley-graph counterexamples with Fourier upper bias
tending to zero. This is the exact starting point for Lemmas 2.2–2.7 in the
compact-Cayley PDF. -/
structure CayleyCounterSeq (ℓ : ℕ) (η : ℝ) where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  T : ∀ n, Finset (ZMod (p n))
  T_sym : ∀ n, SymmetricFinset (T n)
  T_zero : ∀ n, (0 : ZMod (p n)) ∉ T n
  T_density : ∀ n, η * (p n : ℝ) ≤ ((T n).card : ℝ)
  eps : ℕ → ℝ
  eps_pos : ∀ n, 0 < eps n
  eps_tendsto_zero : Tendsto eps atTop (𝓝 0)
  T_fourier_upper : ∀ n,
    letI : NeZero (p n) := ⟨(prime n).ne_zero⟩
    FourierUpperIndicator (T n) (eps n)
  no_clique : ∀ n,
    ¬ ∃ C : Finset (ZMod (p n)), C.card = ℓ ∧ CliqueInCayley (T n) C

/-- Failure of the explicit compact-Cayley statement produces the standard
contradiction sequence with `ε_n = 1 / (n + 1)` and `p_n > n`. -/
theorem exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
    {ℓ : ℕ} {η : ℝ}
    (hfail : ¬ CompactCayleyCliqueStatementExplicit ℓ η) :
    ∃ _S : CayleyCounterSeq ℓ η, True := by
  classical
  have hbad : ∀ n : ℕ,
      ∃ p : ℕ, ∃ hp : p.Prime, n < p ∧
      ∃ T : Finset (ZMod p),
        SymmetricFinset T ∧
        (0 : ZMod p) ∉ T ∧
        η * (p : ℝ) ≤ (T.card : ℝ) ∧
        (letI : NeZero p := ⟨hp.ne_zero⟩;
          FourierUpperIndicator T (((n + 1 : ℕ) : ℝ)⁻¹)) ∧
        ¬ ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
    intro n
    by_contra hnone
    apply hfail
    refine ⟨(((n + 1 : ℕ) : ℝ)⁻¹), by positivity, n, ?_⟩
    intro p hp hpgt T hsym hzero hdens hfourier
    by_contra hNo
    apply hnone
    exact ⟨p, hp, hpgt, T, hsym, hzero, hdens, hfourier, hNo⟩
  choose p hp hpgt T hsym hzero hdens hfourier hnoclique using hbad
  refine ⟨{
    p := p
    prime := hp
    p_gt := hpgt
    T := T
    T_sym := hsym
    T_zero := hzero
    T_density := hdens
    eps := fun n => (((n + 1 : ℕ) : ℝ)⁻¹)
    eps_pos := by
      intro n
      positivity
    eps_tendsto_zero := by
      simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    T_fourier_upper := by
      intro n
      simpa using hfourier n
    no_clique := hnoclique
  }, trivial⟩

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CliqueEndpoint.lean
    ============================================================= -/

/-
Erdős Problem 42 — internal finite lemmas for the compact-Cayley theorem.

This file starts opening the remaining Route B trust boundary
`compact_cayley_clique`.  The lemmas here are finite bookkeeping around the
endpoint of the compactness argument: once counting convergence gives an
ordered tuple whose pairwise differences lie in the allowed set, `0 ∉ T`
turns that tuple into an actual finite clique.
-/

namespace Erdos42.CompactCayley

open Finset Erdos42

/-- An ordered `ℓ`-tuple whose distinct pairwise differences all lie in the
allowed Cayley set `T`. -/
def CliqueTuple {p ℓ : ℕ} (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : Prop :=
  ∀ i j : Fin ℓ, i ≠ j → x i - x j ∈ T

lemma cliqueTuple_injective_of_zero_notMem
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hT0 : (0 : ZMod p) ∉ T) (hx : CliqueTuple T x) :
    Function.Injective x := by
  intro i j hij
  by_contra hne
  have hdiff : x i - x j ∈ T := hx i j hne
  apply hT0
  simpa [hij] using hdiff

/-- A zero-free ordered clique tuple yields the `Finset` clique required by
`compact_cayley_clique`. This is the finite endpoint used after the compact
counting argument proves that at least one ordered clique tuple exists. -/
theorem exists_clique_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hT0 : (0 : ZMod p) ∉ T)
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  let C : Finset (ZMod p) := (Finset.univ : Finset (Fin ℓ)).image x
  have hinj : Function.Injective x :=
    cliqueTuple_injective_of_zero_notMem hT0 hx
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro y hy z hz hyz
    change y ∈ (Finset.univ : Finset (Fin ℓ)).image x at hy
    change z ∈ (Finset.univ : Finset (Fin ℓ)).image x at hz
    rw [Finset.mem_image] at hy hz
    rcases hy with ⟨i, _hi, rfl⟩
    rcases hz with ⟨j, _hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hyz (by simp [hij])
    exact hx i j hij

/-- Boolean-valued indicator for ordered clique tuples, useful when connecting
finite homomorphism densities to actual cliques. -/
noncomputable def cliqueTupleIndicator {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  by
    classical
    exact if CliqueTuple T x then 1 else 0

/-- The finite set of ordered `ℓ`-tuples forming a clique in the Cayley graph. -/
noncomputable def cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : Finset (Fin ℓ → ZMod p) :=
  by
    classical
    exact (Finset.univ : Finset (Fin ℓ → ZMod p)).filter (fun x => CliqueTuple T x)

lemma mem_cliqueTupleFinset {p ℓ : ℕ} [NeZero p]
    {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p} :
    x ∈ cliqueTupleFinset (ℓ := ℓ) T ↔ CliqueTuple T x := by
  classical
  simp [cliqueTupleFinset]

lemma cliqueTupleFinset_nonempty_of_cliqueTuple
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    {x : Fin ℓ → ZMod p} (hx : CliqueTuple T x) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty :=
  ⟨x, mem_cliqueTupleFinset.mpr hx⟩

lemma exists_clique_of_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T)
    (h : (cliqueTupleFinset (ℓ := ℓ) T).Nonempty) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rcases h with ⟨x, hx⟩
  exact exists_clique_of_cliqueTuple hT0 (mem_cliqueTupleFinset.mp hx)

lemma cliqueTupleFinset_nonempty_of_clique
    {p ℓ : ℕ} [NeZero p] {T C : Finset (ZMod p)}
    (hCcard : C.card = ℓ) (hClique : CliqueInCayley T C) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  classical
  let e : C ≃ Fin ℓ := C.equivFinOfCardEq hCcard
  let x : Fin ℓ → ZMod p := fun i => (e.symm i).1
  refine cliqueTupleFinset_nonempty_of_cliqueTuple (T := T) (x := x) ?_
  intro i j hij
  have hxi : x i ∈ C := (e.symm i).2
  have hxj : x j ∈ C := (e.symm j).2
  have hne : x i ≠ x j := by
    intro h
    have hsub : e.symm i = e.symm j := Subtype.ext h
    exact hij (by simpa using congrArg e hsub)
  exact hClique (x i) hxi (x j) hxj hne

lemma cliqueTupleFinset_nonempty_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    (cliqueTupleFinset (ℓ := ℓ) T).Nonempty ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  refine ⟨exists_clique_of_cliqueTupleFinset_nonempty hT0, ?_⟩
  rintro ⟨C, hCcard, hClique⟩
  exact cliqueTupleFinset_nonempty_of_clique hCcard hClique

/-- The edge set of the complete graph on `Fin ℓ`, oriented by the natural
order to avoid double-counting. -/
def cliqueEdgePairs (ℓ : ℕ) : Finset (Fin ℓ × Fin ℓ) :=
  (Finset.univ : Finset (Fin ℓ × Fin ℓ)).filter (fun e => e.1 < e.2)

lemma cliqueEdgePairs_left_lt_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 < e.2 := by
  exact (Finset.mem_filter.mp he).2

lemma cliqueEdgePairs_left_ne_right {ℓ : ℕ} {e : Fin ℓ × Fin ℓ}
    (he : e ∈ cliqueEdgePairs ℓ) : e.1 ≠ e.2 :=
  ne_of_lt (cliqueEdgePairs_left_lt_right he)

lemma cliqueEdgePairs_card_le_sq (ℓ : ℕ) :
    (cliqueEdgePairs ℓ).card ≤ ℓ * ℓ := by
  classical
  unfold cliqueEdgePairs
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin ℓ × Fin ℓ)))
    (p := fun e : Fin ℓ × Fin ℓ => e.1 < e.2)
  simpa [Fintype.card_prod, Fintype.card_fin] using h

/-- Product weight for the finite Cayley `K_ℓ` homomorphism density. For
indicator functions this is `1` exactly on ordered clique tuples and `0`
otherwise, once `T` is symmetric. -/
noncomputable def cliqueKernelWeight {p ℓ : ℕ}
    (T : Finset (ZMod p)) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, indicatorC T (x e.1 - x e.2)

lemma cliqueKernelWeight_eq_one_of_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hx : CliqueTuple T x) :
    cliqueKernelWeight T x = 1 := by
  classical
  unfold cliqueKernelWeight
  apply Finset.prod_eq_one
  intro e he
  have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
  have hmem : x e.1 - x e.2 ∈ T := hx e.1 e.2 (ne_of_lt hlt)
  simp [indicatorC, hmem]

lemma cliqueKernelWeight_eq_zero_of_not_cliqueTuple
    {p ℓ : ℕ} {T : Finset (ZMod p)} {x : Fin ℓ → ZMod p}
    (hTsym : SymmetricFinset T) (hx : ¬ CliqueTuple T x) :
    cliqueKernelWeight T x = 0 := by
  classical
  rw [CliqueTuple, not_forall] at hx
  rcases hx with ⟨i, hx⟩
  rw [not_forall] at hx
  rcases hx with ⟨j, hx⟩
  rw [Classical.not_imp] at hx
  rcases hx with ⟨hij, hnot⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (i, j))
    · simp [cliqueEdgePairs, hlt]
    · simp [indicatorC, hnot]
  · have hnot' : x j - x i ∉ T := by
      intro hji
      have hneg : -(x j - x i) ∈ T := (hTsym (x j - x i)).mp hji
      exact hnot (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg)
    unfold cliqueKernelWeight
    apply Finset.prod_eq_zero (i := (j, i))
    · simp [cliqueEdgePairs, hgt]
    · simp [indicatorC, hnot']

lemma cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric
    {p ℓ : ℕ} {T : Finset (ZMod p)} (hTsym : SymmetricFinset T)
    (x : Fin ℓ → ZMod p) :
    cliqueKernelWeight T x = cliqueTupleIndicator T x := by
  classical
  unfold cliqueTupleIndicator
  by_cases hx : CliqueTuple T x
  · simp [hx, cliqueKernelWeight_eq_one_of_cliqueTuple hx]
  · simp [hx, cliqueKernelWeight_eq_zero_of_not_cliqueTuple hTsym hx]

/-- Ordered clique-tuple count. This is the finite, unnormalized version of the
`K_ℓ` Cayley homomorphism density for indicator functions. -/
noncomputable def cliqueTupleCount {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ∑ x : Fin ℓ → ZMod p, cliqueTupleIndicator T x

lemma cliqueTupleCount_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleCount (ℓ := ℓ) T =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  classical
  rw [cliqueTupleCount]
  change
    (∑ x ∈ (Finset.univ : Finset (Fin ℓ → ZMod p)),
        if CliqueTuple T x then (1 : ℂ) else 0) =
      (((Finset.univ : Finset (Fin ℓ → ZMod p)).filter
        (fun x => CliqueTuple T x)).card : ℂ)
  rw [Finset.sum_boole]

/-- Normalized ordered clique-tuple density. -/
noncomputable def cliqueTupleDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) * cliqueTupleCount (ℓ := ℓ) T

lemma cliqueTupleDensity_eq_card_cliqueTupleFinset
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    cliqueTupleDensity (ℓ := ℓ) T =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ((cliqueTupleFinset (ℓ := ℓ) T).card : ℂ) := by
  simp [cliqueTupleDensity, cliqueTupleCount_eq_card_cliqueTupleFinset]

lemma cliqueTupleDensity_re_eq_card_div
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    (cliqueTupleDensity (ℓ := ℓ) T).re =
      ((cliqueTupleFinset (ℓ := ℓ) T).card : ℝ) /
        (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
  rw [cliqueTupleDensity_eq_card_cliqueTupleFinset]
  have hden :
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) =
        (((Fintype.card (Fin ℓ → ZMod p) : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [hden, Complex.re_ofReal_mul]
  simp [div_eq_inv_mul]

lemma cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      (cliqueTupleFinset (ℓ := ℓ) T).Nonempty := by
  rw [cliqueTupleDensity_re_eq_card_div]
  have hden_pos : 0 < (Fintype.card (Fin ℓ → ZMod p) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin ℓ → ZMod p))
  rw [div_eq_inv_mul, mul_pos_iff_of_pos_left (inv_pos.mpr hden_pos)]
  constructor
  · intro hcard
    exact Finset.card_pos.mp (by exact_mod_cast hcard)
  · intro hnonempty
    exact_mod_cast (Finset.card_pos.mpr hnonempty)

lemma cliqueTupleDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueTupleDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueTupleDensity_re_pos_iff_cliqueTupleFinset_nonempty]
  exact cliqueTupleFinset_nonempty_iff_exists_clique hT0

/-- Product-form `K_ℓ` density, matching the notation in the compact-Cayley
PDF before it is specialized to indicators of Cayley sets. -/
noncomputable def cliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (T : Finset (ZMod p)) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, cliqueKernelWeight T x

lemma cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) :
    cliqueKernelDensity (ℓ := ℓ) T = cliqueTupleDensity (ℓ := ℓ) T := by
  classical
  simp [cliqueKernelDensity, cliqueTupleDensity, cliqueTupleCount,
    cliqueKernelWeight_eq_cliqueTupleIndicator_of_symmetric hTsym]

lemma cliqueKernelDensity_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (cliqueKernelDensity (ℓ := ℓ) T).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [cliqueKernelDensity_eq_cliqueTupleDensity_of_symmetric hTsym]
  exact cliqueTupleDensity_re_pos_iff_exists_clique hT0

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/SpectralCutNorm.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley route, Lemma 2.5 finite spectral layer.

The compact-Cayley proof's Lemma 2.5 is the finite statement that the Cayley
cut norm of a kernel `a(x-y)` is controlled by the largest Fourier coefficient
of `a`.  This file starts that route with the concrete finite objects and the
Fourier expansion of the Cayley kernel. It deliberately introduces no new
assumptions; the operator-norm/Cauchy-Schwarz estimate builds on these
definitions.
-/

namespace Erdos42.CompactCayley

open scoped BigOperators ZMod

/-- Normalized average over `ZMod p`. -/
noncomputable def avgZMod {p : ℕ} [NeZero p] (f : ZMod p → ℂ) : ℂ :=
  ((p : ℂ)⁻¹) * ∑ x : ZMod p, f x

lemma avgZMod_sum {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (F : ι → ZMod p → ℂ) :
    avgZMod (fun x => ∑ i : ι, F i x) = ∑ i : ι, avgZMod (F i) := by
  classical
  unfold avgZMod
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

lemma avgZMod_const_mul {p : ℕ} [NeZero p]
    (c : ℂ) (f : ZMod p → ℂ) :
    avgZMod (fun x => c * f x) = c * avgZMod f := by
  unfold avgZMod
  rw [← Finset.mul_sum]
  ring

lemma avgZMod_mul_const {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (c : ℂ) :
    avgZMod (fun x => f x * c) = avgZMod f * c := by
  unfold avgZMod
  rw [← Finset.sum_mul]
  ring

/-- The finite Cayley cut functional attached to the kernel `a(x-y)` and two
test functions.  Lemma 2.5 takes a supremum of `‖cayleyCutFunctional a φ ψ‖`
over tests bounded by `1`. -/
noncomputable def cayleyCutFunctional {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) : ℂ :=
  avgZMod fun x => avgZMod fun y => a (x - y) * φ x * ψ y

/-- The left test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def leftFourierTest {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun x => ZMod.stdAddChar (r * x) * φ x

/-- The right test Fourier factor appearing after expanding the Cayley kernel. -/
noncomputable def rightFourierTest {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) : ℂ :=
  avgZMod fun y => ZMod.stdAddChar (-(r * y)) * ψ y

lemma rightFourierTest_eq_normalizedDftFunction {p : ℕ} [NeZero p]
    (ψ : ZMod p → ℂ) (r : ZMod p) :
    rightFourierTest ψ r = normalizedDftFunction ψ r := by
  dsimp [rightFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) ψ r]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [mul_comm r y]

lemma leftFourierTest_eq_normalizedDftFunction_neg {p : ℕ} [NeZero p]
    (φ : ZMod p → ℂ) (r : ZMod p) :
    leftFourierTest φ r = normalizedDftFunction φ (-r) := by
  dsimp [leftFourierTest, avgZMod]
  rw [normalizedDftFunction_eq_sum (p := p) φ (-r)]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  congr 1
  simp [mul_comm]

lemma sum_sq_norm_rightFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (ψ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction ψ r‖ ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [rightFourierTest_eq_normalizedDftFunction]

lemma sum_sq_norm_leftFourierTest_eq_normalizedDftFunction
    {p : ℕ} [NeZero p] (φ : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
      ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
  classical
  calc
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) =
        ∑ r : ZMod p, ‖normalizedDftFunction φ (-r)‖ ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [leftFourierTest_eq_normalizedDftFunction_neg]
    _ = ∑ r : ZMod p, ‖normalizedDftFunction φ r‖ ^ 2 := by
          refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ ?_
          intro r
          simp

lemma star_stdAddChar_neg_mul {p : ℕ} [NeZero p] (x r : ZMod p) :
    (starRingEnd ℂ) (ZMod.stdAddChar (-(x * r))) =
      ZMod.stdAddChar (x * r) := by
  have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (x * r)
  simp [h]

lemma star_normalizedDftFunction {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    (starRingEnd ℂ) (normalizedDftFunction f r) =
      ((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (x * r) * (starRingEnd ℂ) (f x) := by
  rw [normalizedDftFunction_eq_sum]
  simp [map_sum, star_stdAddChar_neg_mul, mul_comm]

lemma avg_stdAddChar_mul_star_eq_star_normalizedDftFunction
    {p : ℕ} [NeZero p] (g : ZMod p → ℂ) (r : ZMod p) :
    avgZMod (fun x => ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x)) =
      (starRingEnd ℂ) (normalizedDftFunction g r) := by
  rw [star_normalizedDftFunction, avgZMod]
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [mul_comm r x]

/-- Parseval cross identity in normalized-average form. -/
lemma avg_mul_star_eq_sum_normalizedDftFunction {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) :
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
      ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
  classical
  calc
    avgZMod (fun x => f x * (starRingEnd ℂ) (g x)) =
        avgZMod
          (fun x =>
            (∑ r : ZMod p, ZMod.stdAddChar (r * x) * normalizedDftFunction f r) *
              (starRingEnd ℂ) (g x)) := by
          congr 1
          funext x
          rw [← function_eq_sum_normalizedDftFunction (p := p) f x]
    _ = avgZMod
          (fun x =>
            ∑ r : ZMod p,
              normalizedDftFunction f r *
                (ZMod.stdAddChar (r * x) * (starRingEnd ℂ) (g x))) := by
          congr 1
          funext x
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro r _
          ring
    _ = ∑ r : ZMod p,
        normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction g r) := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul, avg_stdAddChar_mul_star_eq_star_normalizedDftFunction]

/-- Parseval in the normalized convention used here. -/
lemma sum_sq_norm_normalizedDftFunction_eq_avg
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) =
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  classical
  apply Complex.ofReal_injective
  have hcomplex :
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
        ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
    calc
      ((p : ℂ)⁻¹) * ∑ x : ZMod p, (‖f x‖ : ℂ) ^ 2 =
          avgZMod (fun x => f x * (starRingEnd ℂ) (f x)) := by
            unfold avgZMod
            apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [← Complex.mul_conj']
      _ = ∑ r : ZMod p,
          normalizedDftFunction f r * (starRingEnd ℂ) (normalizedDftFunction f r) :=
            avg_mul_star_eq_sum_normalizedDftFunction f f
      _ = ∑ r : ZMod p, (‖normalizedDftFunction f r‖ : ℂ) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro r _
            rw [Complex.mul_conj']
  simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_natCast] using hcomplex.symm

lemma sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {f : ZMod p → ℂ}
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    (∑ r : ZMod p, ‖normalizedDftFunction f r‖ ^ 2) ≤ 1 := by
  classical
  rw [sum_sq_norm_normalizedDftFunction_eq_avg]
  have hsum : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ) := by
    calc
      (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ ∑ _x : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro x _
        have hx_nonneg : 0 ≤ ‖f x‖ := norm_nonneg _
        have hx_le : ‖f x‖ ^ 2 ≤ (1 : ℝ) := by
          nlinarith [hf x]
        exact hx_le
      _ = (p : ℝ) := by simp [ZMod.card]
  have hp_nonneg : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr (Nat.cast_nonneg p)
  have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  calc
    ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ ^ 2
        ≤ ((p : ℝ)⁻¹) * (p : ℝ) := mul_le_mul_of_nonneg_left hsum hp_nonneg
    _ = 1 := inv_mul_cancel₀ hp_ne

lemma sum_sq_norm_rightFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {ψ : ZMod p → ℂ}
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_rightFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hψ

lemma sum_sq_norm_leftFourierTest_le_one_of_norm_le_one
    {p : ℕ} [NeZero p] {φ : ZMod p → ℂ}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1 := by
  rw [sum_sq_norm_leftFourierTest_eq_normalizedDftFunction]
  exact sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one hφ

lemma stdAddChar_mul_sub {p : ℕ} [NeZero p] (r x y : ZMod p) :
    ZMod.stdAddChar (r * (x - y)) =
      ZMod.stdAddChar (r * x) * ZMod.stdAddChar (-(r * y)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

/-- Fourier inversion applied to the Cayley kernel `a(x-y)`, in the exact
factorized form used by the spectral-cut argument. -/
lemma cayleyKernel_eq_fourier_sum {p : ℕ} [NeZero p]
    (a : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
  calc
    a (x - y) =
        ∑ r : ZMod p, ZMod.stdAddChar (r * (x - y)) *
          normalizedDftFunction a r := by
          exact function_eq_sum_normalizedDftFunction (p := p) a (x - y)
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r *
          ZMod.stdAddChar (r * x) *
          ZMod.stdAddChar (-(r * y)) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [stdAddChar_mul_sub]
          ring

/-- The same kernel expansion with the two test functions multiplied in. -/
lemma cayleyKernel_mul_tests_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) (x y : ZMod p) :
    a (x - y) * φ x * ψ y =
      ∑ r : ZMod p,
        normalizedDftFunction a r *
          (ZMod.stdAddChar (r * x) * φ x) *
          (ZMod.stdAddChar (-(r * y)) * ψ y) := by
  rw [cayleyKernel_eq_fourier_sum (p := p) a x y]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro r _
  ring

/-- The double-average Cayley cut functional factors through the normalized
Fourier coefficients of the kernel and the two test Fourier factors.  This is
the algebraic core of the spectral cut-norm bound in compact-Cayley Lemma 2.5. -/
lemma cayleyCutFunctional_eq_fourier_sum {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    cayleyCutFunctional a φ ψ =
      ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
  classical
  unfold cayleyCutFunctional
  simp_rw [cayleyKernel_mul_tests_eq_fourier_sum (p := p) a φ ψ]
  calc
    avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ∑ r : ZMod p,
                normalizedDftFunction a r *
                  (ZMod.stdAddChar (r * x) * φ x) *
                  (ZMod.stdAddChar (-(r * y)) * ψ y))) =
        avgZMod
          (fun x : ZMod p =>
            ∑ r : ZMod p,
              normalizedDftFunction a r *
                (ZMod.stdAddChar (r * x) * φ x) *
                rightFourierTest ψ r) := by
          congr 1
          funext x
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_const_mul]
          simp [rightFourierTest, mul_assoc]
    _ = ∑ r : ZMod p,
        normalizedDftFunction a r * leftFourierTest φ r * rightFourierTest ψ r := by
          rw [avgZMod_sum]
          refine Finset.sum_congr rfl ?_
          intro r _
          rw [avgZMod_mul_const, avgZMod_const_mul]
          simp [leftFourierTest, mul_assoc]

/-- Immediate `L¹` Fourier bound for the Cayley cut functional.  Lemma 2.5
will sharpen this to the spectral supremum under `‖φ‖∞, ‖ψ‖∞ ≤ 1`, using the
Hilbert-space/operator-norm argument from the compact-Cayley PDF. -/
lemma norm_cayleyCutFunctional_le_fourier_l1 {p : ℕ} [NeZero p]
    (a φ ψ : ZMod p → ℂ) :
    ‖cayleyCutFunctional a φ ψ‖ ≤
      ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * ‖leftFourierTest φ r‖ *
          ‖rightFourierTest ψ r‖ := by
  rw [cayleyCutFunctional_eq_fourier_sum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro r _
  rw [norm_mul, norm_mul]

/-- Cauchy-Schwarz sharpening of the Fourier `L¹` bound, assuming the two
test-factor Fourier `L²` sums are at most `1`.  This is the finite analytic
core that remains after Parseval supplies those two `L²` hypotheses from
`‖φ‖∞, ‖ψ‖∞ ≤ 1`. -/
lemma norm_cayleyCutFunctional_le_spectral_of_fourier_l2
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ2 : (∑ r : ZMod p, ‖leftFourierTest φ r‖ ^ 2) ≤ 1)
    (hψ2 : (∑ r : ZMod p, ‖rightFourierTest ψ r‖ ^ 2) ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  classical
  let L : ZMod p → ℝ := fun r => ‖leftFourierTest φ r‖
  let R : ZMod p → ℝ := fun r => ‖rightFourierTest ψ r‖
  have h_l1 :
      ‖cayleyCutFunctional a φ ψ‖ ≤ ∑ r : ZMod p,
        ‖normalizedDftFunction a r‖ * L r * R r := by
    simpa [L, R, mul_assoc] using norm_cayleyCutFunctional_le_fourier_l1 a φ ψ
  have h_by_M :
      ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r ≤
        ∑ r : ZMod p, M * (L r * R r) := by
    refine Finset.sum_le_sum ?_
    intro r _
    have hLR : 0 ≤ L r * R r := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc
      ‖normalizedDftFunction a r‖ * L r * R r =
          ‖normalizedDftFunction a r‖ * (L r * R r) := by ring
      _ ≤ M * (L r * R r) := mul_le_mul_of_nonneg_right (hM r) hLR
  have hcs :
      ∑ r : ZMod p, L r * R r ≤
        Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) := by
    simpa [L, R] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (ZMod p)) L R)
  have hsqrtL : Real.sqrt (∑ r : ZMod p, L r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [L] using hφ2
  have hsqrtR : Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    simpa [R] using hψ2
  have hsqrt_nonneg_L : 0 ≤ Real.sqrt (∑ r : ZMod p, L r ^ 2) := Real.sqrt_nonneg _
  have hsqrt_nonneg_R : 0 ≤ Real.sqrt (∑ r : ZMod p, R r ^ 2) := Real.sqrt_nonneg _
  have hprod :
      Real.sqrt (∑ r : ZMod p, L r ^ 2) *
          Real.sqrt (∑ r : ZMod p, R r ^ 2) ≤ 1 := by
    nlinarith
  have hsumLR : ∑ r : ZMod p, L r * R r ≤ 1 := hcs.trans hprod
  calc
    ‖cayleyCutFunctional a φ ψ‖
        ≤ ∑ r : ZMod p, ‖normalizedDftFunction a r‖ * L r * R r := h_l1
    _ ≤ ∑ r : ZMod p, M * (L r * R r) := h_by_M
    _ = M * ∑ r : ZMod p, L r * R r := by rw [Finset.mul_sum]
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left hsumLR hMnonneg
    _ = M := by ring

/-- Finite spectral cut-norm control for one pair of bounded test functions.

This is the usable Lemma 2.5 core for the compact-Cayley route: if every
normalized Fourier coefficient of the Cayley kernel `a` has norm at most `M`,
then every double average against tests bounded by `1` has norm at most `M`. -/
lemma norm_cayleyCutFunctional_le_spectral
    {p : ℕ} [NeZero p] (a φ ψ : ZMod p → ℂ) {M : ℝ}
    (hM : ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M)
    (hMnonneg : 0 ≤ M)
    (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hψ : ∀ y, ‖ψ y‖ ≤ 1) :
    ‖cayleyCutFunctional a φ ψ‖ ≤ M := by
  exact norm_cayleyCutFunctional_le_spectral_of_fourier_l2 a φ ψ hM hMnonneg
    (sum_sq_norm_leftFourierTest_le_one_of_norm_le_one hφ)
    (sum_sq_norm_rightFourierTest_le_one_of_norm_le_one hψ)

/-- Predicate form of the spectral coefficient bound. -/
def SpectralBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ r : ZMod p, ‖normalizedDftFunction a r‖ ≤ M

/-- Predicate form of the Cayley cut-norm bound: every double average against
tests bounded by `1` has norm at most `M`. -/
def CayleyCutBound {p : ℕ} [NeZero p] (a : ZMod p → ℂ) (M : ℝ) : Prop :=
  ∀ φ ψ : ZMod p → ℂ,
    (∀ x, ‖φ x‖ ≤ 1) → (∀ y, ‖ψ y‖ ≤ 1) →
      ‖cayleyCutFunctional a φ ψ‖ ≤ M

/-- Compact-Cayley Lemma 2.5 in predicate form. -/
theorem cayleyCutBound_of_spectralBound
    {p : ℕ} [NeZero p] (a : ZMod p → ℂ) {M : ℝ}
    (hMnonneg : 0 ≤ M) (hM : SpectralBound a M) :
    CayleyCutBound a M := by
  intro φ ψ hφ hψ
  exact norm_cayleyCutFunctional_le_spectral a φ ψ hM hMnonneg hφ hψ

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CountingConvergence.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite density target for compact-Cayley counting convergence.

This file does not prove the compactness/counting-convergence lemma yet.  It
sets up the exact finite `K_ℓ` density that Lemma 2.6 should converge to, and
connects its indicator-specialized form to the existing finite clique endpoint.
-/

namespace Erdos42.CompactCayley

open Finset Erdos42 Filter
open scoped Topology

/-- Normalized average over a nonempty finite type.  This is used for the
remaining coordinates after a single clique edge has been isolated. -/
noncomputable def avgFinite (α : Type*) [Fintype α] (f : α → ℂ) : ℂ :=
  ((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x

lemma norm_avgFinite_le {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℂ} {M : ℝ} (hf : ∀ x, ‖f x‖ ≤ M) :
    ‖avgFinite α f‖ ≤ M := by
  classical
  have hcard_pos_nat : 0 < Fintype.card α := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hcard_pos_nat
  have hsum :
      ‖∑ x : α, f x‖ ≤ (Fintype.card α : ℝ) * M := by
    calc
      ‖∑ x : α, f x‖ ≤ ∑ x : α, ‖f x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : α, M := by
        exact Finset.sum_le_sum (fun x _hx => hf x)
      _ = (Fintype.card α : ℝ) * M := by simp
  unfold avgFinite
  calc
    ‖((Fintype.card α : ℂ)⁻¹) * ∑ x : α, f x‖
        = ‖((Fintype.card α : ℂ)⁻¹)‖ * ‖∑ x : α, f x‖ := norm_mul _ _
    _ ≤ ‖((Fintype.card α : ℂ)⁻¹)‖ * ((Fintype.card α : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = M := by
      rw [norm_inv, Complex.norm_natCast]
      field_simp [ne_of_gt hcard_pos]

/-- Averaging Cayley cut functionals over a nonempty finite parameter set does
not increase a uniform Cayley cut bound.  This is the reusable analytic estimate
for one-edge replacement after the remaining vertices are frozen. -/
lemma norm_avgFinite_cayleyCutFunctional_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} [NeZero p] {a : ZMod p → ℂ} {M : ℝ}
    (hcut : CayleyCutBound a M)
    (φ ψ : ι → ZMod p → ℂ)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖avgFinite ι (fun t => cayleyCutFunctional a (φ t) (ψ t))‖ ≤ M := by
  exact norm_avgFinite_le (fun t => hcut (φ t) (ψ t) (hφ t) (hψ t))

/-- Indices other than the two endpoints of a chosen clique edge. -/
def EdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Type :=
  {k : Fin ℓ // k ≠ e₀.1 ∧ k ≠ e₀.2}

instance instFintypeEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    Fintype (EdgeRest e₀) := by
  classical
  unfold EdgeRest
  infer_instance

noncomputable instance instDecidableEqEdgeRest {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) :
    DecidableEq (EdgeRest e₀) := by
  classical
  infer_instance

/-- Assignments to all non-endpoint coordinates of a chosen clique edge. -/
abbrev EdgeRestAssignment (p ℓ : ℕ) (e₀ : Fin ℓ × Fin ℓ) : Type :=
  EdgeRest e₀ → ZMod p

noncomputable instance instFintypeEdgeRestAssignment {p ℓ : ℕ} [NeZero p]
    (e₀ : Fin ℓ × Fin ℓ) : Fintype (EdgeRestAssignment p ℓ e₀) := by
  unfold EdgeRestAssignment
  infer_instance

/-- Extend a frozen assignment on the remaining vertices by assigning `u` and
`v` to the two endpoints of the chosen edge. -/
noncomputable def extendEdgeTuple {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) : Fin ℓ → ZMod p :=
  fun k =>
    if h1 : k = e₀.1 then u
    else if h2 : k = e₀.2 then v
    else r ⟨k, h1, h2⟩

@[simp] lemma extendEdgeTuple_left {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 = u := by
  simp [extendEdgeTuple]

@[simp] lemma extendEdgeTuple_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.2 ≠ e₀.1) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.2 = v := by
  simp [extendEdgeTuple, hne]

lemma extendEdgeTuple_rest {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p)
    {k : Fin ℓ} (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = r ⟨k, h1, h2⟩ := by
  simp [extendEdgeTuple, h1, h2]

lemma extendEdgeTuple_edge_diff {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v := by
  simp [extendEdgeTuple_right (e₀ := e₀) (show e₀.2 ≠ e₀.1 from hne.symm)]

lemma extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs {p ℓ : ℕ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    extendEdgeTuple e₀ r u v e₀.1 - extendEdgeTuple e₀ r u v e₀.2 = u - v :=
  extendEdgeTuple_edge_diff (cliqueEdgePairs_left_ne_right he₀) r u v

/-- An edge is incident to a vertex. -/
def edgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) : Prop :=
  e.1 = i ∨ e.2 = i

instance instDecidableEdgeUsesVertex {ℓ : ℕ} (e : Fin ℓ × Fin ℓ) (i : Fin ℓ) :
    Decidable (edgeUsesVertex e i) := by
  unfold edgeUsesVertex
  infer_instance

/-- All clique edges except the edge currently being replaced. -/
def remainingCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  cliqueEdgePairs ℓ \ {e₀}

/-- Remaining clique edges incident to the left endpoint of the replaced edge. -/
def leftCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter (fun e => edgeUsesVertex e e₀.1)

/-- Remaining clique edges incident to the right endpoint but not the left
endpoint of the replaced edge. -/
def rightCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ edgeUsesVertex e e₀.2)

/-- Remaining clique edges incident to neither endpoint of the replaced edge. -/
def constantCliqueEdges {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ) : Finset (Fin ℓ × Fin ℓ) :=
  (remainingCliqueEdges e₀).filter
    (fun e => ¬ edgeUsesVertex e e₀.1 ∧ ¬ edgeUsesVertex e e₀.2)

lemma edge_not_uses_both_endpoints_of_mem_remaining {ℓ : ℕ}
    {e₀ e : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (he : e ∈ remainingCliqueEdges e₀)
    (hleft : edgeUsesVertex e e₀.1) (hright : edgeUsesVertex e e₀.2) : False := by
  have he_pair : e ∈ cliqueEdgePairs ℓ := (Finset.mem_sdiff.mp he).1
  have hne_single : e ∉ ({e₀} : Finset (Fin ℓ × Fin ℓ)) := (Finset.mem_sdiff.mp he).2
  have hlt_e : e.1 < e.2 := cliqueEdgePairs_left_lt_right he_pair
  have hlt_e₀ : e₀.1 < e₀.2 := cliqueEdgePairs_left_lt_right he₀
  rcases hleft with hleft | hleft <;> rcases hright with hright | hright
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq
  · have h_eq : e = e₀ := Prod.ext hleft hright
    exact hne_single (by simp [h_eq])
  · have hbad : e₀.2 < e₀.1 := by simpa [hleft, hright] using hlt_e
    exact (not_lt_of_ge (le_of_lt hlt_e₀)) hbad
  · have h_eq : e₀.1 = e₀.2 := hleft.symm.trans hright
    exact (ne_of_lt hlt_e₀) h_eq

lemma extendEdgeTuple_eq_of_same_left {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v v' : ZMod p) {k : Fin ℓ}
    (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u v' k := by
  by_cases h1 : k = e₀.1
  · subst h1
    simp [extendEdgeTuple]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u v' h1 h2]

lemma extendEdgeTuple_eq_of_same_right {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u u' v : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v k := by
  by_cases h2 : k = e₀.2
  · subst h2
    simp [extendEdgeTuple, h1]
  · rw [extendEdgeTuple_rest e₀ r u v h1 h2,
      extendEdgeTuple_rest e₀ r u' v h1 h2]

lemma extendEdgeTuple_eq_of_not_endpoints {p ℓ : ℕ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v u' v' : ZMod p) {k : Fin ℓ}
    (h1 : k ≠ e₀.1) (h2 : k ≠ e₀.2) :
    extendEdgeTuple e₀ r u v k = extendEdgeTuple e₀ r u' v' k := by
  rw [extendEdgeTuple_rest e₀ r u v h1 h2,
    extendEdgeTuple_rest e₀ r u' v' h1 h2]

/-- Product over remaining edges incident to the left endpoint.  It only
depends on the left endpoint variable. -/
noncomputable def remainingLeftTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) : ℂ :=
  ∏ e ∈ leftCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)

/-- Product over remaining edges incident to the right endpoint but not the
left endpoint.  It only depends on the right endpoint variable. -/
noncomputable def remainingRightTest {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) : ℂ :=
  ∏ e ∈ rightCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)

/-- Product over remaining edges incident to neither endpoint.  It is constant
in the two active endpoint variables once the rest assignment is fixed. -/
noncomputable def remainingConstFactor {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (r : EdgeRestAssignment p ℓ e₀) : ℂ :=
  ∏ e ∈ constantCliqueEdges e₀,
    F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)

lemma prod_remainingCliqueEdges_split {ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (H : Fin ℓ × Fin ℓ → ℂ) :
    (∏ e ∈ remainingCliqueEdges e₀, H e) =
      (∏ e ∈ leftCliqueEdges e₀, H e) *
        (∏ e ∈ rightCliqueEdges e₀, H e) *
          (∏ e ∈ constantCliqueEdges e₀, H e) := by
  classical
  unfold leftCliqueEdges rightCliqueEdges constantCliqueEdges
  let s := remainingCliqueEdges e₀
  let P : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.1
  let Q : Fin ℓ × Fin ℓ → Prop := fun e => edgeUsesVertex e e₀.2
  have h1 := Finset.prod_filter_mul_prod_filter_not (s := s) (p := P) (f := H)
  have h2 := Finset.prod_filter_mul_prod_filter_not
    (s := s.filter (fun e => ¬ P e)) (p := Q) (f := H)
  dsimp [P, Q, s] at h1 h2 ⊢
  rw [← h1]
  rw [← h2]
  simp [Finset.filter_filter, mul_assoc]

lemma prod_leftCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ leftCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingLeftTest F e₀ r u := by
  classical
  unfold remainingLeftTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have he_rem : e ∈ remainingCliqueEdges e₀ := (Finset.mem_filter.mp he).1
  have hleft : edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := by
    intro hright
    exact edge_not_uses_both_endpoints_of_mem_remaining he₀ he_rem hleft hright
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_same_left r u v 0 hnr.1,
    extendEdgeTuple_eq_of_same_left r u v 0 hnr.2]

lemma prod_rightCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ rightCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingRightTest F e₀ r v := by
  classical
  unfold remainingRightTest
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnl := not_or.mp hnot_left
  rw [extendEdgeTuple_eq_of_same_right r u 0 v hnl.1,
    extendEdgeTuple_eq_of_same_right r u 0 v hnl.2]

lemma prod_constantCliqueEdges_actual_eq {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (r : EdgeRestAssignment p ℓ e₀) (u v : ZMod p) :
    (∏ e ∈ constantCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
    remainingConstFactor F e₀ r := by
  classical
  unfold remainingConstFactor
  refine Finset.prod_congr rfl ?_
  intro e he
  have hnot_left : ¬ edgeUsesVertex e e₀.1 := (Finset.mem_filter.mp he).2.1
  have hnot_right : ¬ edgeUsesVertex e e₀.2 := (Finset.mem_filter.mp he).2.2
  have hnl := not_or.mp hnot_left
  have hnr := not_or.mp hnot_right
  rw [extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.1 hnr.1,
    extendEdgeTuple_eq_of_not_endpoints r u v 0 0 hnl.2 hnr.2]

lemma remainingCliqueEdgeProduct_factorization {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (r : EdgeRestAssignment p ℓ e₀)
    (u v : ZMod p) :
    (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
        (remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u) *
          remainingRightTest F e₀ r v := by
  classical
  change (∏ e ∈ remainingCliqueEdges e₀,
      F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) = _
  rw [prod_remainingCliqueEdges_split]
  rw [prod_leftCliqueEdges_actual_eq he₀ r u v,
    prod_rightCliqueEdges_actual_eq r u v,
    prod_constantCliqueEdges_actual_eq r u v]
  ring

/-- Reindex all clique tuples by a chosen edge's two endpoint values and the
assignment on the remaining vertices. -/
noncomputable def edgeTupleEquiv {p ℓ : ℕ} (e₀ : Fin ℓ × Fin ℓ)
    (hne : e₀.1 ≠ e₀.2) :
    (Fin ℓ → ZMod p) ≃ (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) where
  toFun x := (fun k => x k.1, x e₀.1, x e₀.2)
  invFun q := extendEdgeTuple e₀ q.1 q.2.1 q.2.2
  left_inv x := by
    funext k
    by_cases h1 : k = e₀.1
    · subst h1
      simp [extendEdgeTuple]
    · by_cases h2 : k = e₀.2
      · subst h2
        simp [extendEdgeTuple, hne.symm]
      · simp [extendEdgeTuple, h1, h2]
  right_inv q := by
    rcases q with ⟨r, u, v⟩
    ext k
    · exact extendEdgeTuple_rest e₀ r u v k.property.1 k.property.2
    · simp [extendEdgeTuple]
    · simp [extendEdgeTuple, hne.symm]

lemma sum_edgeTupleEquiv {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ}
    (hne : e₀.1 ≠ e₀.2) (f : (Fin ℓ → ZMod p) → ℂ) :
    (∑ x : Fin ℓ → ZMod p, f x) =
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        f (extendEdgeTuple e₀ q.1 q.2.1 q.2.2) := by
  simpa [edgeTupleEquiv] using ((edgeTupleEquiv (p := p) e₀ hne).symm.sum_comp f).symm

/-- The normalized tuple average, after reindexing at one chosen edge, is the
average over frozen remaining coordinates of a two-variable normalized
average. -/
lemma edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    {p ℓ : ℕ} [NeZero p] {e₀ : Fin ℓ × Fin ℓ} (hne : e₀.1 ≠ e₀.2)
    (H : EdgeRestAssignment p ℓ e₀ → ZMod p → ZMod p → ℂ) :
    ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
      ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
        H q.1 q.2.1 q.2.2 =
    avgFinite (EdgeRestAssignment p ℓ e₀)
      (fun r => avgZMod fun u => avgZMod fun v => H r u v) := by
  classical
  have hcard_nat :
      Fintype.card (Fin ℓ → ZMod p) =
        Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
    calc
      Fintype.card (Fin ℓ → ZMod p) =
          Fintype.card (EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p) :=
            Fintype.card_congr (edgeTupleEquiv (p := p) e₀ hne)
      _ = Fintype.card (EdgeRestAssignment p ℓ e₀) * p * p := by
            simp [Fintype.card_prod, ZMod.card, mul_assoc]
  have hcard_complex :
      (Fintype.card (Fin ℓ → ZMod p) : ℂ) =
        (Fintype.card (EdgeRestAssignment p ℓ e₀) : ℂ) * (p : ℂ) * (p : ℂ) := by
    exact_mod_cast hcard_nat
  unfold avgFinite avgZMod
  rw [hcard_complex]
  simp only [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

/-- Product weight for the finite Cayley `K_ℓ` density with an arbitrary complex
kernel `f`.  The compact-Cayley counting convergence lemma should produce
positivity of the density built from this generic kernel, before specializing
`f` to an indicator. -/
noncomputable def finiteCliqueKernelWeight {p ℓ : ℕ}
    (f : ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, f (x e.1 - x e.2)

/-- Normalized finite `K_ℓ` Cayley density for an arbitrary kernel on `ZMod p`. -/
noncomputable def finiteCliqueKernelDensity {p ℓ : ℕ} [NeZero p]
    (f : ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeight f x

/-- Edge-indexed version of the finite Cayley `K_ℓ` product weight.  This is
the natural bookkeeping object for the telescoping proof of counting
convergence, where one edge kernel is replaced at a time. -/
noncomputable def finiteCliqueKernelWeightEdge {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (x : Fin ℓ → ZMod p) : ℂ :=
  ∏ e ∈ cliqueEdgePairs ℓ, F e (x e.1 - x e.2)

/-- Edge-indexed normalized finite `K_ℓ` Cayley density. -/
noncomputable def finiteCliqueKernelDensityEdge {p ℓ : ℕ} [NeZero p]
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : ℂ :=
  ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
    ∑ x : Fin ℓ → ZMod p, finiteCliqueKernelWeightEdge F x

lemma finiteCliqueKernelDensityEdge_const
    {p ℓ : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (ℓ := ℓ) (fun _ => f) =
      finiteCliqueKernelDensity (ℓ := ℓ) f := by
  rfl

/-- Every edge kernel is uniformly bounded by `1`. -/
def EdgeKernelBoundedByOne {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) : Prop :=
  ∀ e z, ‖F e z‖ ≤ 1

/-- Replace one edge kernel in an edge-indexed kernel family. -/
noncomputable def replaceEdgeKernel {p ℓ : ℕ}
    (F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (e₀ : Fin ℓ × Fin ℓ)
    (g : ZMod p → ℂ) : (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e = e₀ then g z else F e z

lemma EdgeKernelBoundedByOne.const {p ℓ : ℕ} {f : ZMod p → ℂ}
    (hf : ∀ z, ‖f z‖ ≤ 1) :
    EdgeKernelBoundedByOne (ℓ := ℓ) (fun _ => f) := by
  intro _ z
  exact hf z

lemma EdgeKernelBoundedByOne.replace {p ℓ : ℕ}
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    EdgeKernelBoundedByOne (replaceEdgeKernel F e₀ g) := by
  intro e z
  by_cases h : e = e₀
  · simp [replaceEdgeKernel, h, hg z]
  · simp [replaceEdgeKernel, h, hF e z]

lemma norm_remainingLeftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingLeftTest F e₀ r u‖ ≤ 1 := by
  classical
  unfold remainingLeftTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r u 0 e.1 - extendEdgeTuple e₀ r u 0 e.2))

lemma norm_remainingRightTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (v : ZMod p) :
    ‖remainingRightTest F e₀ r v‖ ≤ 1 := by
  classical
  unfold remainingRightTest
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 v e.1 - extendEdgeTuple e₀ r 0 v e.2))

lemma norm_remainingConstFactor_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) :
    ‖remainingConstFactor F e₀ r‖ ≤ 1 := by
  classical
  unfold remainingConstFactor
  rw [norm_prod]
  exact Finset.prod_le_one
    (fun e _he =>
      norm_nonneg
        (F e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2)))
    (fun e _he =>
      hF e (extendEdgeTuple e₀ r 0 0 e.1 - extendEdgeTuple e₀ r 0 0 e.2))

lemma norm_remainingConstFactor_mul_leftTest_le_one {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} (hF : EdgeKernelBoundedByOne F)
    (e₀ : Fin ℓ × Fin ℓ) (r : EdgeRestAssignment p ℓ e₀) (u : ZMod p) :
    ‖remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u‖ ≤ 1 := by
  rw [norm_mul]
  have hc := norm_remainingConstFactor_le_one hF e₀ r
  have hl := norm_remainingLeftTest_le_one hF e₀ r u
  have hcn : 0 ≤ ‖remainingConstFactor F e₀ r‖ := norm_nonneg _
  have hln : 0 ≤ ‖remainingLeftTest F e₀ r u‖ := norm_nonneg _
  nlinarith

lemma finiteCliqueKernelWeightEdge_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge F x =
      F e₀ (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  unfold finiteCliqueKernelWeightEdge
  exact Finset.prod_eq_mul_prod_sdiff_singleton_of_mem he₀
    (fun e => F e (x e.1 - x e.2))

lemma finiteCliqueKernelWeightEdge_replace_eq_single_mul
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x =
      g (x e₀.1 - x e₀.2) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  classical
  rw [finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  congr 1
  · simp [replaceEdgeKernel]
  · refine Finset.prod_congr rfl ?_
    intro e he
    have hne : e ≠ e₀ := by
      intro h
      exact (Finset.mem_sdiff.mp he).2 (by simp [h])
    simp [replaceEdgeKernel, hne]

/-- Pointwise single-edge replacement identity, used by the telescoping proof of
finite counting convergence. -/
lemma finiteCliqueKernelWeightEdge_replace_sub
    {p ℓ : ℕ} {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) (x : Fin ℓ → ZMod p) :
    finiteCliqueKernelWeightEdge (replaceEdgeKernel F e₀ g) x -
        finiteCliqueKernelWeightEdge F x =
      (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  rw [finiteCliqueKernelWeightEdge_replace_eq_single_mul he₀,
    finiteCliqueKernelWeightEdge_eq_single_mul he₀]
  ring

/-- Density-level form of the single-edge replacement identity. -/
lemma finiteCliqueKernelDensityEdge_replace_sub
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin ℓ → ZMod p,
          (g (x e₀.1 - x e₀.2) - F e₀ (x e₀.1 - x e₀.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀}, F e (x e.1 - x e.2) := by
  unfold finiteCliqueKernelDensityEdge
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  exact finiteCliqueKernelWeightEdge_replace_sub he₀ g x

/-- Reindexed density-level single-edge replacement identity.  The full tuple
sum is rewritten as a sum over frozen non-endpoint coordinates and the two
endpoint variables. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_reindex
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      ((Fintype.card (Fin ℓ → ZMod p) : ℂ)⁻¹) *
        ∑ q : EdgeRestAssignment p ℓ e₀ × ZMod p × ZMod p,
          (g (q.2.1 - q.2.2) - F e₀ (q.2.1 - q.2.2)) *
            ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
              F e (extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.1 -
                extendEdgeTuple e₀ q.1 q.2.1 q.2.2 e.2) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub he₀]
  congr 1
  rw [sum_edgeTupleEquiv (cliqueEdgePairs_left_ne_right he₀)]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [extendEdgeTuple_edge_diff_of_mem_cliqueEdgePairs he₀]

/-- If the remaining-edge product factors into a left test and a right test
after the chosen edge has been isolated, then the single-edge replacement
difference is exactly an average of Cayley cut functionals. -/
lemma finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
    {p ℓ : ℕ} [NeZero p] {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ}
    {e₀ : Fin ℓ × Fin ℓ} (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (g : ZMod p → ℂ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v) :
    finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F =
      avgFinite (EdgeRestAssignment p ℓ e₀)
        (fun r => cayleyCutFunctional
          (fun z => g z - F e₀ z) (φ r) (ψ r)) := by
  rw [finiteCliqueKernelDensityEdge_replace_sub_reindex he₀]
  rw [edgeTuple_normalized_sum_eq_avgFinite_avgZMod
    (p := p) (ℓ := ℓ) (e₀ := e₀) (cliqueEdgePairs_left_ne_right he₀)
    (fun r u v =>
      (g (u - v) - F e₀ (u - v)) *
        ∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
          F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2))]
  unfold cayleyCutFunctional
  congr 1
  funext r
  congr 1
  funext u
  congr 1
  funext v
  rw [hprod]
  ring

/-- One-edge replacement estimate, assuming the tuple-sum difference has already
been rewritten as an average of Cayley cut functionals over the frozen remaining
coordinates.  The remaining work for Lemma 2.6 is to supply this representation
for the concrete edge being replaced. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (φ ψ : ι → ZMod p → ℂ)
    (hrepr :
      finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
          finiteCliqueKernelDensityEdge F =
        avgFinite ι
          (fun t => cayleyCutFunctional
            (fun z => g z - F e₀ z) (φ t) (ψ t)))
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  rw [hrepr]
  exact norm_avgFinite_cayleyCutFunctional_le hcut φ ψ hφ hψ

/-- One-edge replacement estimate from a concrete factorization of the
remaining-edge product into two bounded test functions. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (φ ψ : EdgeRestAssignment p ℓ e₀ → ZMod p → ℂ)
    (hprod : ∀ r u v,
      (∏ e ∈ cliqueEdgePairs ℓ \ {e₀},
        F e (extendEdgeTuple e₀ r u v e.1 - extendEdgeTuple e₀ r u v e.2)) =
          φ r u * ψ r v)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M)
    (hφ : ∀ t x, ‖φ t x‖ ≤ 1)
    (hψ : ∀ t y, ‖ψ t y‖ ≤ 1) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cut_representation φ ψ
    (finiteCliqueKernelDensityEdge_replace_sub_eq_avgFinite_cayleyCutFunctional_of_factorization
      he₀ g φ ψ hprod)
    hcut hφ hψ

/-- Concrete one-edge replacement estimate: if all unreplaced edge kernels are
bounded by `1`, then replacing one edge is controlled by the Cayley cut bound of
the replacement difference. -/
lemma norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound
    {p ℓ : ℕ} [NeZero p]
    {F : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {e₀ : Fin ℓ × Fin ℓ}
    {g : ZMod p → ℂ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ)
    (hF : EdgeKernelBoundedByOne F)
    (hcut : CayleyCutBound (fun z => g z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (replaceEdgeKernel F e₀ g) -
        finiteCliqueKernelDensityEdge F‖ ≤ M := by
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_factorization he₀
    (fun r u => remainingConstFactor F e₀ r * remainingLeftTest F e₀ r u)
    (fun r v => remainingRightTest F e₀ r v)
    (by intro r u v; exact remainingCliqueEdgeProduct_factorization he₀ r u v)
    hcut
    (by intro r u; exact norm_remainingConstFactor_mul_leftTest_le_one hF e₀ r u)
    (by intro r v; exact norm_remainingRightTest_le_one hF e₀ r v)

/-- Patch an edge-indexed kernel family by replacing the kernels on `S` with
those from another family. -/
noncomputable def patchEdgeKernel {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ)) :
    (Fin ℓ × Fin ℓ) → ZMod p → ℂ :=
  fun e z => if e ∈ S then G e z else F e z

lemma patchEdgeKernel_insert_eq_replace {p ℓ : ℕ}
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) (S : Finset (Fin ℓ × Fin ℓ))
    (e₀ : Fin ℓ × Fin ℓ) :
    patchEdgeKernel F G (insert e₀ S) =
      replaceEdgeKernel (patchEdgeKernel F G S) e₀ (G e₀) := by
  funext e z
  by_cases h : e = e₀
  · subst h
    simp [patchEdgeKernel, replaceEdgeKernel]
  · simp [patchEdgeKernel, replaceEdgeKernel, h]

lemma EdgeKernelBoundedByOne.patch {p ℓ : ℕ}
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G) :
    EdgeKernelBoundedByOne (patchEdgeKernel F G S) := by
  intro e z
  by_cases h : e ∈ S
  · simp [patchEdgeKernel, h, hG e z]
  · simp [patchEdgeKernel, h, hF e z]

lemma finiteCliqueKernelDensityEdge_patch_empty {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (∅ : Finset (Fin ℓ × Fin ℓ))) =
      finiteCliqueKernelDensityEdge F := by
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  simp [patchEdgeKernel]

lemma finiteCliqueKernelDensityEdge_patch_all {p ℓ : ℕ} [NeZero p]
    (F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ) :
    finiteCliqueKernelDensityEdge (patchEdgeKernel F G (cliqueEdgePairs ℓ)) =
      finiteCliqueKernelDensityEdge G := by
  classical
  unfold finiteCliqueKernelDensityEdge finiteCliqueKernelWeightEdge
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  refine Finset.prod_congr rfl ?_
  intro e he
  simp [patchEdgeKernel, he]

lemma norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {S : Finset (Fin ℓ × Fin ℓ)}
    {e₀ : Fin ℓ × Fin ℓ} {M : ℝ}
    (he₀ : e₀ ∈ cliqueEdgePairs ℓ) (heS : e₀ ∉ S)
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : CayleyCutBound (fun z => G e₀ z - F e₀ z) M) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e₀ S)) -
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ ≤ M := by
  rw [patchEdgeKernel_insert_eq_replace]
  exact norm_finiteCliqueKernelDensityEdge_replace_sub_le_of_cutBound he₀
    (EdgeKernelBoundedByOne.patch hF hG)
    (by simpa [patchEdgeKernel, heS] using hcut)

/-- Finite telescoping estimate for compact-Cayley Lemma 2.6.  Replacing all
edge kernels changes the finite `K_ℓ` density by at most the number of clique
edges times a uniform Cayley cut bound. -/
lemma norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M)
    (S : Finset (Fin ℓ × Fin ℓ)) (hS : S ⊆ cliqueEdgePairs ℓ) :
    ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
        finiteCliqueKernelDensityEdge F‖ ≤ (S.card : ℝ) * M := by
  classical
  refine Finset.induction_on S ?base ?step hS
  · intro _hS
    rw [finiteCliqueKernelDensityEdge_patch_empty]
    simp
  · intro e S heS ih hInsert
    have heClique : e ∈ cliqueEdgePairs ℓ := hInsert (by simp)
    have hSsub : S ⊆ cliqueEdgePairs ℓ := by
      intro x hx
      exact hInsert (by simp [hx])
    have hstep := norm_finiteCliqueKernelDensityEdge_patch_insert_sub_le
      (F := F) (G := G) (S := S) (e₀ := e) heClique heS hF hG (hcut e heClique)
    have hih := ih hSsub
    have hdecomp :
        finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge F =
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F) := by
      ring
    rw [hdecomp]
    calc
      ‖(finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)) +
          (finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
            finiteCliqueKernelDensityEdge F)‖
          ≤ ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G (insert e S)) -
            finiteCliqueKernelDensityEdge (patchEdgeKernel F G S)‖ +
            ‖finiteCliqueKernelDensityEdge (patchEdgeKernel F G S) -
              finiteCliqueKernelDensityEdge F‖ := norm_add_le _ _
      _ ≤ M + (S.card : ℝ) * M := add_le_add hstep hih
      _ = ((insert e S).card : ℝ) * M := by
        rw [Finset.card_insert_of_notMem heS]
        norm_num
        ring

lemma norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound {p ℓ : ℕ} [NeZero p]
    {F G : (Fin ℓ × Fin ℓ) → ZMod p → ℂ} {M : ℝ}
    (hF : EdgeKernelBoundedByOne F) (hG : EdgeKernelBoundedByOne G)
    (hcut : ∀ e ∈ cliqueEdgePairs ℓ, CayleyCutBound (fun z => G e z - F e z) M) :
    ‖finiteCliqueKernelDensityEdge G - finiteCliqueKernelDensityEdge F‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  have h := norm_finiteCliqueKernelDensityEdge_patch_sub_le_card_mul
    (F := F) (G := G) (M := M) hF hG hcut (cliqueEdgePairs ℓ) (by intro x hx; exact hx)
  rwa [finiteCliqueKernelDensityEdge_patch_all] at h

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hcut : CayleyCutBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  simpa [finiteCliqueKernelDensityEdge_const] using
    norm_finiteCliqueKernelDensityEdge_sub_le_card_mul_cutBound
      (F := fun _ : Fin ℓ × Fin ℓ => f) (G := fun _ : Fin ℓ × Fin ℓ => g)
      (M := M)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hf)
      (EdgeKernelBoundedByOne.const (ℓ := ℓ) hg)
      (fun _e _he => hcut)

lemma norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    {p ℓ : ℕ} [NeZero p] {f g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hf : ∀ z, ‖f z‖ ≤ 1) (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => g z - f z) M) :
    ‖finiteCliqueKernelDensity (ℓ := ℓ) g - finiteCliqueKernelDensity (ℓ := ℓ) f‖ ≤
      ((cliqueEdgePairs ℓ).card : ℝ) * M := by
  exact norm_finiteCliqueKernelDensity_sub_le_card_mul_cutBound
    (ℓ := ℓ) hf hg
    (cayleyCutBound_of_spectralBound (a := fun z => g z - f z) hMnonneg hspec)

lemma indicatorC_norm_le_one {p : ℕ} (T : Finset (ZMod p)) (z : ZMod p) :
    ‖indicatorC T z‖ ≤ 1 := by
  classical
  by_cases h : z ∈ T
  · simp [indicatorC, h]
  · simp [indicatorC, h]

lemma finiteCliqueKernelDensity_indicatorC
    {p ℓ : ℕ} [NeZero p] (T : Finset (ZMod p)) :
    finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) =
      cliqueKernelDensity (ℓ := ℓ) T := by
  rfl

/-- Indicator-specialized finite generic density is positive exactly when the
finite Cayley graph contains a clique. -/
lemma finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T) :
    0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re ↔
      ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  rw [finiteCliqueKernelDensity_indicatorC]
  exact cliqueKernelDensity_re_pos_iff_exists_clique hTsym hT0

/-- Positive finite generic density for the indicator kernel gives the finite
clique needed by the compact-Cayley theorem.  This is the endpoint that the
future counting-convergence proof should feed into. -/
theorem exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    (hdensity : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  exact (finiteCliqueKernelDensity_indicatorC_re_pos_iff_exists_clique hTsym hT0).mp hdensity

/-- Finite endpoint for the compact counting transfer: if a bounded model
kernel has positive finite `K_ℓ` density by more than the spectral-transfer
error, and it is spectrally close to `1_T`, then `T` contains a clique. -/
theorem exists_clique_of_spectral_density_transfer
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((cliqueEdgePairs ℓ).card : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hclose := norm_finiteCliqueKernelDensity_sub_le_card_mul_spectralBound
    (ℓ := ℓ) hMnonneg hg (indicatorC_norm_le_one T) hspec
  have hre_abs :
      |(finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re| ≤
        ((cliqueEdgePairs ℓ).card : ℝ) * M := by
    exact le_trans (Complex.abs_re_le_norm _) hclose
  have hre_low :
      -(((cliqueEdgePairs ℓ).card : ℝ) * M) ≤
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
          finiteCliqueKernelDensity (ℓ := ℓ) g).re :=
    (abs_le.mp hre_abs).1
  have hpos : 0 < (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re := by
    have hcalc :
        (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T)).re =
          (finiteCliqueKernelDensity (ℓ := ℓ) g).re +
            (finiteCliqueKernelDensity (ℓ := ℓ) (indicatorC T) -
              finiteCliqueKernelDensity (ℓ := ℓ) g).re := by
      simp
    rw [hcalc]
    linarith
  exact exists_clique_of_finiteCliqueKernelDensity_indicator_re_pos hTsym hT0 hpos

/-- Same finite endpoint with the rough bound `#E(K_ℓ) ≤ ℓ²`, avoiding exact
edge-count bookkeeping at higher compactness layers. -/
theorem exists_clique_of_spectral_density_transfer_sq
    {p ℓ : ℕ} [NeZero p] {T : Finset (ZMod p)}
    (hTsym : SymmetricFinset T) (hT0 : (0 : ZMod p) ∉ T)
    {g : ZMod p → ℂ} {M : ℝ}
    (hMnonneg : 0 ≤ M)
    (hg : ∀ z, ‖g z‖ ≤ 1)
    (hspec : SpectralBound (fun z => indicatorC T z - g z) M)
    (hdensity : ((ℓ * ℓ : ℕ) : ℝ) * M <
      (finiteCliqueKernelDensity (ℓ := ℓ) g).re) :
    ∃ C : Finset (ZMod p), C.card = ℓ ∧ CliqueInCayley T C := by
  have hcard : ((cliqueEdgePairs ℓ).card : ℝ) ≤ ((ℓ * ℓ : ℕ) : ℝ) := by
    exact_mod_cast cliqueEdgePairs_card_le_sq ℓ
  exact exists_clique_of_spectral_density_transfer hTsym hT0 hMnonneg hg hspec
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hMnonneg) hdensity)

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Subseq.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley counterexample subsequences.

Fourier extraction repeatedly passes to strictly monotone subsequences.  This
file keeps that bookkeeping out of the later compactness files.
-/

namespace Erdos42.CompactCayley

open Filter
open scoped Topology

/-- Pass a compact-Cayley counterexample sequence to a strictly monotone
subsequence. -/
def CayleyCounterSeq.subseq
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    CayleyCounterSeq ℓ η where
  p n := S.p (φ n)
  prime n := S.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero =>
          exact Nat.zero_le _
      | succ n ih =>
          have hstep : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
          omega
    exact lt_of_le_of_lt hn_le_φn (S.p_gt (φ n))
  T n := S.T (φ n)
  T_sym n := S.T_sym (φ n)
  T_zero n := S.T_zero (φ n)
  T_density n := S.T_density (φ n)
  eps n := S.eps (φ n)
  eps_pos n := S.eps_pos (φ n)
  eps_tendsto_zero := by
    exact S.eps_tendsto_zero.comp hφ.tendsto_atTop
  T_fourier_upper n := by
    simpa using S.T_fourier_upper (φ n)
  no_clique n := S.no_clique (φ n)

@[simp] lemma CayleyCounterSeq.subseq_p
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).p n = S.p (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_T
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).T n = S.T (φ n) := rfl

@[simp] lemma CayleyCounterSeq.subseq_eps
    {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subseq φ hφ).eps n = S.eps (φ n) := rfl

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/FourierExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — generic finite Fourier extraction primitives.

This is the first compact-Cayley assumption-removal layer.  It deliberately avoids
clique-specific definitions: a `FourierSeq` is only a bounded sequence of
complex-valued functions on prime cyclic groups.  Later compact-Cayley
extraction specializes it to the indicators of the counterexample sets.
-/

namespace Erdos42.CompactCayley

open Finset Erdos42
open scoped BigOperators Topology

/-- A bounded sequence of functions on prime cyclic groups. -/
structure FourierSeq where
  p : ℕ → ℕ
  prime : ∀ n, (p n).Prime
  p_gt : ∀ n, n < p n
  h : ∀ n, ZMod (p n) → ℂ
  h_bound : ∀ n x, ‖h n x‖ ≤ 1

/-- Pass a generic Fourier sequence to a strictly monotone subsequence. -/
def FourierSeq.subseq
    (F : FourierSeq) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    FourierSeq where
  p n := F.p (φ n)
  prime n := F.prime (φ n)
  p_gt n := by
    have hn_le_φn : n ≤ φ n := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self n)))
    exact lt_of_le_of_lt hn_le_φn (F.p_gt (φ n))
  h n := F.h (φ n)
  h_bound n x := F.h_bound (φ n) x

/-- The Fourier sequence attached to a compact-Cayley counterexample sequence:
the functions are indicators of the allowed Cayley difference sets. -/
noncomputable def CayleyCounterSeq.toFourierSeq
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    FourierSeq where
  p := S.p
  prime := S.prime
  p_gt := S.p_gt
  h n := indicatorC (S.T n)
  h_bound n x := by
    classical
    by_cases hx : x ∈ S.T n <;> simp [indicatorC, hx]

/-- Normalized Fourier coefficient of the `n`-th function in a `FourierSeq`. -/
noncomputable def FourierSeq.coeff
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) : ℂ :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  normalizedDftFunction (F.h n) r

/-- Parseval bound for a bounded `FourierSeq` term. -/
lemma FourierSeq.sum_sq_norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    (∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2) ≤ 1 := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simpa [FourierSeq.coeff] using
    (sum_sq_norm_normalizedDftFunction_le_one_of_norm_le_one
      (p := F.p n) (f := F.h n) (F.h_bound n))

/-- Pointwise normalized Fourier coefficients of a bounded `FourierSeq` are
bounded by `1`. -/
lemma FourierSeq.norm_coeff_le_one
    (F : FourierSeq) (n : ℕ) (r : ZMod (F.p n)) :
    ‖F.coeff n r‖ ≤ 1 := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hsum := F.sum_sq_norm_coeff_le_one n
  have hterm :
      ‖F.coeff n r‖ ^ 2 ≤
        ∑ s : ZMod (F.p n), ‖F.coeff n s‖ ^ 2 :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset (ZMod (F.p n))))
      (f := fun s : ZMod (F.p n) => ‖F.coeff n s‖ ^ 2)
      (fun _s _hs => sq_nonneg _) (Finset.mem_univ r)
  have hsquare : ‖F.coeff n r‖ ^ 2 ≤ 1 := hterm.trans hsum
  have habs : |‖F.coeff n r‖| ≤ 1 :=
    (sq_le_one_iff_abs_le_one _).mp hsquare
  simpa [abs_of_nonneg (norm_nonneg _)] using habs

/-- Large spectrum at threshold `q⁻¹`. -/
noncomputable def FourierSeq.largeSpectrum
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    Finset (ZMod (F.p n)) :=
  letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  (Finset.univ : Finset (ZMod (F.p n))).filter
    (fun r => ((q : ℝ)⁻¹) < ‖F.coeff n r‖)

lemma FourierSeq.mem_largeSpectrum
    {F : FourierSeq} {q : ℕ+} {n : ℕ} {r : ZMod (F.p n)} :
    r ∈ F.largeSpectrum q n ↔ ((q : ℝ)⁻¹) < ‖F.coeff n r‖ := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  simp [FourierSeq.largeSpectrum]

lemma FourierSeq.largeSpectrum_subset_univ
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    F.largeSpectrum q n ⊆ (Finset.univ : Finset (ZMod (F.p n))) := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  intro r _hr
  simp

lemma FourierSeq.largeSpectrum_card_mul_sq_le_sum_sq
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    letI : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 ≤
      ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  calc
    ((F.largeSpectrum q n).card : ℝ) * ((q : ℝ)⁻¹) ^ 2 =
        ∑ r ∈ F.largeSpectrum q n, ((q : ℝ)⁻¹) ^ 2 := by
          simp [mul_comm]
    _ ≤ ∑ r ∈ F.largeSpectrum q n, ‖F.coeff n r‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hlt : ((q : ℝ)⁻¹) < ‖F.coeff n r‖ :=
            FourierSeq.mem_largeSpectrum.mp hr
          have hq_nonneg : 0 ≤ ((q : ℝ)⁻¹) := by positivity
          have hnorm_nonneg : 0 ≤ ‖F.coeff n r‖ := norm_nonneg _
          have hle_abs : |((q : ℝ)⁻¹)| ≤ |‖F.coeff n r‖| := by
            rw [abs_of_nonneg hq_nonneg, abs_of_nonneg hnorm_nonneg]
            exact le_of_lt hlt
          exact sq_le_sq.mpr hle_abs
    _ ≤ ∑ r : ZMod (F.p n), ‖F.coeff n r‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (F.largeSpectrum_subset_univ q n)
            (by intro r _hrUniv _hrNotLarge; exact sq_nonneg _)

/-- Parseval cardinality bound for the large spectrum at threshold `q⁻¹`. -/
lemma FourierSeq.largeSpectrum_card_le
    (F : FourierSeq) (q : ℕ+) (n : ℕ) :
    (F.largeSpectrum q n).card ≤ (q : ℕ) ^ 2 := by
  let : NeZero (F.p n) := ⟨(F.prime n).ne_zero⟩
  have hmass :=
    (F.largeSpectrum_card_mul_sq_le_sum_sq q n).trans
      (F.sum_sq_norm_coeff_le_one n)
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hτsq_pos : 0 < ((q : ℝ)⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr hq_pos)
  have hreal :
      ((F.largeSpectrum q n).card : ℝ) ≤ ((q : ℝ) ^ 2) := by
    calc
      ((F.largeSpectrum q n).card : ℝ) ≤
          1 / (((q : ℝ)⁻¹) ^ 2) := by
            exact (le_div_iff₀ hτsq_pos).mpr (by simpa [mul_comm] using hmass)
      _ = (q : ℝ) ^ 2 := by
            field_simp [hq_pos.ne']
  have hreal_nat :
      ((F.largeSpectrum q n).card : ℝ) ≤ (((q : ℕ) ^ 2 : ℕ) : ℝ) := by
    simpa using hreal
  exact_mod_cast hreal_nat

/-! ## Finite large-spectrum labelling -/

/-- A fixed countable label type large enough to label every threshold-large
frequency, for every `n`, without needing cardinalities to stabilize. -/
abbrev LargeLabel : Type :=
  Sigma fun q : ℕ+ => Fin ((q : ℕ) ^ 2 + 1)

/-- A finite set of cardinality at most `m` can be covered by a map from
`Fin m`.  Extra indices may repeat an arbitrary default value. -/
lemma exists_cover_map_of_card_le
    {α : Type*} [Inhabited α] (s : Finset α) (m : ℕ)
    (hcard : s.card ≤ m) :
    ∃ f : Fin m → α, ∀ x ∈ s, ∃ i : Fin m, f i = x := by
  classical
  let f : Fin m → α := fun i =>
    if h : (i : ℕ) < s.card then
      ((Finset.equivFin s).symm ⟨i, h⟩).1
    else default
  refine ⟨f, ?_⟩
  intro x hx
  let xs : s := ⟨x, hx⟩
  let j : Fin s.card := Finset.equivFin s xs
  let i : Fin m := ⟨j, lt_of_lt_of_le j.2 hcard⟩
  refine ⟨i, ?_⟩
  have hi : (i : ℕ) < s.card := j.2
  have hfin : (⟨(i : ℕ), hi⟩ : Fin s.card) = j := by
    ext
    rfl
  have hpre :
      (Finset.equivFin s).symm ⟨(i : ℕ), hi⟩ = xs := by
    rw [hfin]
    dsimp [j]
    simp
  simp [f, i, hi, hpre, xs]

/-- A canonical, choice-based frequency assignment for all large-spectrum
labels of a fixed `FourierSeq`. -/
noncomputable def FourierSeq.largeSpectrumLabelFreq
    (F : FourierSeq) (label : LargeLabel) (n : ℕ) :
    ZMod (F.p n) :=
  let q := label.1
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  cover label.2

/-- Every threshold-large frequency is represented by one of the fixed labels
at that threshold. -/
lemma FourierSeq.exists_largeSpectrumLabelFreq_eq_of_mem
    (F : FourierSeq) (q : ℕ+) (n : ℕ) {r : ZMod (F.p n)}
    (hr : r ∈ F.largeSpectrum q n) :
    ∃ k : Fin ((q : ℕ) ^ 2 + 1),
      F.largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
  classical
  unfold FourierSeq.largeSpectrumLabelFreq
  let m := (q : ℕ) ^ 2 + 1
  let cover :=
    Classical.choose
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  have hcover :
      ∀ x ∈ F.largeSpectrum q n, ∃ i : Fin m, cover i = x :=
    Classical.choose_spec
      (exists_cover_map_of_card_le (s := F.largeSpectrum q n) m (by
        have hcard := F.largeSpectrum_card_le q n
        omega))
  rcases hcover r hr with ⟨k, hk⟩
  exact ⟨k, hk⟩

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/ExtractionGroup.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley extraction quotient skeleton.

This file implements the formal free-abelian word lifts and the eventual-kernel
quotient used by the compact dual construction.  It intentionally stops before
the diagonal stability layer: without eventual zero/nonzero stabilization one
can define the quotient and its basic equality API, but not yet prove the
finite-lift injectivity-on-finite-sets facts needed later.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

/-- Formal integer combinations of compact-Cayley large-spectrum labels. -/
abbrev ExtractionFreeGroup : Type :=
  FreeAbelianGroup LargeLabel

instance extractionFreeGroupCountable : Countable ExtractionFreeGroup := by
  dsimp [ExtractionFreeGroup, LargeLabel]
  infer_instance

/-- Finite lift homomorphism of a formal label combination to the `n`-th
cyclic group. -/
noncomputable def FourierSeq.wordLiftHom
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p n) :=
  FreeAbelianGroup.lift fun label : LargeLabel => labelFreq label n

/-- Finite lift of a formal label combination. -/
noncomputable def FourierSeq.wordLift
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    ZMod (F.p n) :=
  F.wordLiftHom labelFreq n w

lemma FourierSeq.wordLiftHom_apply_of
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (n : ℕ) (label : LargeLabel) :
    F.wordLiftHom labelFreq n (FreeAbelianGroup.of label) =
      labelFreq label n := by
  simp [FourierSeq.wordLiftHom]

lemma FourierSeq.wordLift_add
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w v : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (w + v) n =
      F.wordLift labelFreq w n + F.wordLift labelFreq v n := by
  simp [FourierSeq.wordLift]

lemma FourierSeq.wordLift_neg
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (w : ExtractionFreeGroup) (n : ℕ) :
    F.wordLift labelFreq (-w) n =
      -F.wordLift labelFreq w n := by
  simp [FourierSeq.wordLift]

/-- Formal combinations whose finite lifts vanish eventually. -/
def FourierSeq.eventualKernel
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddSubgroup ExtractionFreeGroup where
  carrier := {w | ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0}
  zero_mem' := by
    simp [FourierSeq.wordLift]
  add_mem' := by
    intro w v hw hv
    filter_upwards [hw, hv] with n hwn hvn
    simp [FourierSeq.wordLift_add, hwn, hvn]
  neg_mem' := by
    intro w hw
    filter_upwards [hw] with n hwn
    simp [FourierSeq.wordLift_neg, hwn]

lemma FourierSeq.mem_eventualKernel_iff
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    w ∈ F.eventualKernel labelFreq ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 :=
  Iff.rfl

/-- Discrete quotient group produced by the compact-Cayley extraction
skeleton.  Its Pontryagin dual is the future compact limit group. -/
abbrev FourierSeq.ExtractionGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) : Type :=
  ExtractionFreeGroup ⧸ F.eventualKernel labelFreq

instance FourierSeq.extractionGroupAddCommGroup
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    AddCommGroup (F.ExtractionGroup labelFreq) :=
  inferInstance

instance FourierSeq.extractionGroupCountable
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    Countable (F.ExtractionGroup labelFreq) :=
  (QuotientAddGroup.mk'_surjective (F.eventualKernel labelFreq)).countable

/-- Quotient equality is exactly eventual equality of finite lifts. -/
lemma FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) =
        QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n =
        F.wordLift labelFreq v n := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp only [FourierSeq.mem_eventualKernel_iff, AddMonoidHom.map_sub,
    FourierSeq.wordLift, sub_eq_zero]

/-- A quotient class is zero exactly when its finite lifts are eventually zero. -/
lemma FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : F.ExtractionGroup labelFreq) = 0 ↔
      ∀ᶠ n in atTop, F.wordLift labelFreq w n = 0 := by
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/StableExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley diagonal extraction data.

The free-abelian extraction group from `ExtractionGroup` only becomes useful
after passing to a subsequence where every formal finite-lift zero relation is
eventually stable and every formal Fourier coefficient converges.  This file
packages that diagonal step for a generic `FourierSeq`.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

/-- Closed unit disk, used as a compact target for countable diagonal
subsequence extraction. -/
abbrev ClosedUnitDisk : Type :=
  {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

lemma compactSpace_closedUnitDisk : CompactSpace ClosedUnitDisk := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    ProperSpace.isCompact_closedBall (0 : ℂ) 1
  exact isCompact_iff_compactSpace.mp hK

lemma exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
    {ι : Type*} [Countable ι] (a : ι → ℕ → ℂ)
    (ha : ∀ i n, ‖a i n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, ∃ z : ℂ,
        Tendsto (fun n => a i (φ n)) atTop (𝓝 z) := by
  let x : ℕ → (ι → ClosedUnitDisk) := fun n i =>
    ⟨a i n, by
      rw [Metric.mem_closedBall, _root_.dist_zero_right]
      exact ha i n⟩
  let : CompactSpace ClosedUnitDisk := compactSpace_closedUnitDisk
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  refine ⟨(y i : ℂ), ?_⟩
  have hcont :
      Continuous (fun y : ι → ClosedUnitDisk => ((y i : ClosedUnitDisk) : ℂ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hi := (hcont.tendsto y).comp hlim
  simpa [x, Function.comp_def] using hi

/-- Countable diagonal stabilization for decidable relations.  This is the
relation-theoretic companion to coefficient convergence: after passing to one
subsequence, every countably indexed yes/no relation is eventually constantly
true or eventually constantly false. -/
lemma exists_strictMono_subseq_eventually_const_countable_family
    {ι : Type*} [Countable ι] (P : ι → ℕ → Prop)
    :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i : ι, (∀ᶠ n in atTop, P i (φ n)) ∨
        (∀ᶠ n in atTop, ¬ P i (φ n)) := by
  classical
  let x : ℕ → (ι → Bool) := fun n i => decide (P i n)
  rcases CompactSpace.tendsto_subseq x with ⟨y, φ, hφ, hlim⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hcont : Continuous (fun y : ι → Bool => y i) := continuous_apply i
  have hi : Tendsto (fun n => x (φ n) i) atTop (𝓝 (y i)) :=
    (hcont.tendsto y).comp hlim
  have hmem : ({y i} : Set Bool) ∈ 𝓝 (y i) := by
    exact (isOpen_discrete ({y i} : Set Bool)).mem_nhds rfl
  have hmem' : ∀ᶠ n in atTop, x (φ n) i ∈ ({y i} : Set Bool) :=
    hi.eventually hmem
  have heq : ∀ᶠ n in atTop, x (φ n) i = y i := by
    filter_upwards [hmem'] with n hn
    simpa using hn
  cases hy : y i
  · right
    filter_upwards [heq] with n hn
    simpa [x, hy] using hn
  · left
    filter_upwards [heq] with n hn
    simpa [x, hy] using hn

/-- Relabel a label-frequency assignment after passing a `FourierSeq` to a
subsequence. -/
def FourierSeq.subseqLabelFreq
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    LargeLabel → ∀ n, ZMod ((F.subseq φ hφ).p n) :=
  fun label n => labelFreq label (φ n)

/-- A fully diagonalized compact-Cayley Fourier extraction package for a fixed
label-frequency assignment.

The subsequence `φ` is still recorded explicitly because later Cayley
specialization will pass the whole counterexample sequence through the same
subsequence. -/
structure FourierSeq.StableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) where
  φ : ℕ → ℕ
  strictMono_φ : StrictMono φ
  finiteLift_eventually_stable : ∀ w : ExtractionFreeGroup,
    (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) = 0) ∨
      (∀ᶠ n in atTop, F.wordLift labelFreq w (φ n) ≠ 0)
  coeffLimit : ExtractionFreeGroup → ℂ
  coeffLimit_tendsto : ∀ w : ExtractionFreeGroup,
    Tendsto
      (fun n =>
        letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩;
        F.coeff (φ n) (F.wordLift labelFreq w (φ n)))
      atTop (𝓝 (coeffLimit w))

/-- Countable diagonal extraction for all formal finite-lift zero relations
and all formal Fourier coefficients. -/
theorem FourierSeq.exists_stableSubseqData
    (F : FourierSeq) (labelFreq : LargeLabel → ∀ n, ZMod (F.p n)) :
    ∃ _data : F.StableSubseqData labelFreq, True := by
  classical
  let P : ExtractionFreeGroup → ℕ → Prop :=
    fun w n => F.wordLift labelFreq w n = 0
  rcases
      exists_strictMono_subseq_eventually_const_countable_family
        P with
    ⟨φ, hφ, hstable⟩
  let a : ExtractionFreeGroup → ℕ → ℂ := fun w n =>
    letI : NeZero (F.p (φ n)) := ⟨(F.prime (φ n)).ne_zero⟩
    F.coeff (φ n) (F.wordLift labelFreq w (φ n))
  have ha : ∀ w n, ‖a w n‖ ≤ 1 := by
    intro w n
    dsimp [a]
    exact F.norm_coeff_le_one (φ n) (F.wordLift labelFreq w (φ n))
  rcases
      exists_strictMono_subseq_tendsto_countable_family_of_norm_le_one
        a ha with
    ⟨ψ, hψ, hconv⟩
  let χ : ℕ → ℕ := fun n => φ (ψ n)
  have hstrict : StrictMono χ := by
    simpa [χ, Function.comp_def] using hφ.comp hψ
  have hstable' : ∀ w : ExtractionFreeGroup,
      (∀ᶠ n in atTop, F.wordLift labelFreq w (χ n) = 0) ∨
        (∀ᶠ n in atTop, F.wordLift labelFreq w (χ n) ≠ 0) := by
    intro w
    rcases hstable w with hzero | hnonzero
    · exact Or.inl (by
        filter_upwards [hψ.tendsto_atTop.eventually hzero] with n hn
        change F.wordLift labelFreq w (φ (ψ n)) = 0
        simpa [P] using hn)
    · exact Or.inr (by
        filter_upwards [hψ.tendsto_atTop.eventually hnonzero] with n hn
        change F.wordLift labelFreq w (φ (ψ n)) ≠ 0
        simpa [P] using hn)
  have hcoeff : ∀ w : ExtractionFreeGroup, ∃ z : ℂ,
      Tendsto
        (fun n =>
          (letI : NeZero (F.p (χ n)) :=
              ⟨(F.prime (χ n)).ne_zero⟩;
            F.coeff (χ n)
              (F.wordLift labelFreq w (χ n))))
        atTop (𝓝 z) := by
    intro w
    rcases hconv w with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    simpa [a, χ] using hz
  choose coeffLimit hcoeffLimit using hcoeff
  refine ⟨{
    φ := χ
    strictMono_φ := hstrict
    finiteLift_eventually_stable := hstable'
    coeffLimit := coeffLimit
    coeffLimit_tendsto := hcoeffLimit
  }, trivial⟩

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/QuotientLift.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite lifts from the compact-Cayley extraction quotient.

Stable extraction data selects a subsequence.  The quotient group used later is
the extraction quotient of that subsequenced `FourierSeq`; finite lifts of
quotient elements use arbitrary representatives, so all algebraic facts are
recorded as eventual statements.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- The Fourier sequence after applying the stable extraction subsequence. -/
def seq (data : F.StableSubseqData labelFreq) : FourierSeq :=
  F.subseq data.φ data.strictMono_φ

/-- The label frequencies transported to the stable extraction subsequence. -/
def subseqLabelFreq (data : F.StableSubseqData labelFreq) :
    LargeLabel → ∀ n, ZMod ((data.seq).p n) :=
  F.subseqLabelFreq labelFreq data.φ data.strictMono_φ

/-- The discrete extraction quotient attached to stable compact-Cayley data. -/
abbrev Group (data : F.StableSubseqData labelFreq) : Type :=
  (data.seq).ExtractionGroup data.subseqLabelFreq

instance (data : F.StableSubseqData labelFreq) :
    Countable data.Group :=
  FourierSeq.extractionGroupCountable data.seq data.subseqLabelFreq

/-- Finite lift homomorphism for formal words along the stable subsequence. -/
noncomputable def finiteLiftHom
    (data : F.StableSubseqData labelFreq) (n : ℕ) :
    ExtractionFreeGroup →+ ZMod (F.p (data.φ n)) :=
  (data.seq).wordLiftHom data.subseqLabelFreq n

lemma finiteLiftHom_apply
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (w : ExtractionFreeGroup) :
    data.finiteLiftHom n w = F.wordLift labelFreq w (data.φ n) := by
  rfl

/-- Chosen finite lift of a quotient frequency. -/
noncomputable def finiteLift
    (data : F.StableSubseqData labelFreq) (n : ℕ)
    (γ : data.Group) :
    ZMod (F.p (data.φ n)) :=
  data.finiteLiftHom n (Quotient.out γ)

/-- Quotient equality is eventual equality of chosen finite lifts of formal
representatives, along the stable subsequence. -/
lemma quotient_eq_iff_eventually_lift_eq
    (data : F.StableSubseqData labelFreq)
    {w v : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = QuotientAddGroup.mk v ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = data.finiteLiftHom n v := by
  rw [FourierSeq.extractionQuotient_eq_iff_eventually_lift_eq
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A quotient class is zero exactly when its representative lift vanishes
eventually. -/
lemma quotient_eq_zero_iff_eventually_lift_eq_zero
    (data : F.StableSubseqData labelFreq)
    {w : ExtractionFreeGroup} :
    (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  rw [FourierSeq.extractionQuotient_eq_zero_iff_eventually_lift_eq_zero
    (F := data.seq) (labelFreq := data.subseqLabelFreq)]
  rfl

/-- A chosen quotient representative has the same finite lift as any specified
representative of the same quotient class, eventually. -/
lemma finiteLift_mk_eventually_eq
    (data : F.StableSubseqData labelFreq) (w : ExtractionFreeGroup) :
    ∀ᶠ n in atTop,
      data.finiteLift n (QuotientAddGroup.mk w : data.Group) =
        data.finiteLiftHom n w := by
  exact (data.quotient_eq_iff_eventually_lift_eq
    (w := Quotient.out (QuotientAddGroup.mk w : data.Group)) (v := w)).mp
    (Quotient.out_eq _)

lemma finiteLift_zero_eventually_eq_zero
    (data : F.StableSubseqData labelFreq) :
    ∀ᶠ n in atTop, data.finiteLift n (0 : data.Group) = 0 := by
  simpa [finiteLift] using
    (data.quotient_eq_zero_iff_eventually_lift_eq_zero
      (w := Quotient.out (0 : data.Group))).mp
      (Quotient.out_eq (0 : data.Group))

lemma finiteLift_add_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ + δ) =
        data.finiteLift n γ + data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ + δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ + Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ + δ))
      (v := Quotient.out γ + Quotient.out δ)).mp hquot] with n hn
  change data.finiteLiftHom n (Quotient.out (γ + δ)) =
    data.finiteLiftHom n (Quotient.out γ) + data.finiteLiftHom n (Quotient.out δ)
  rw [hn]
  exact (data.finiteLiftHom n).map_add _ _

lemma finiteLift_neg_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (-γ) = -data.finiteLift n γ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (-γ)) : data.Group) =
        QuotientAddGroup.mk (-Quotient.out γ) := by
    simp [Quotient.out_eq γ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (-γ)) (v := -Quotient.out γ)).mp hquot] with n hn
  change data.finiteLiftHom n (Quotient.out (-γ)) =
    -data.finiteLiftHom n (Quotient.out γ)
  rw [hn]
  exact (data.finiteLiftHom n).map_neg _

lemma finiteLift_sub_eventually_eq
    (data : F.StableSubseqData labelFreq) (γ δ : data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (γ - δ) =
        data.finiteLift n γ - data.finiteLift n δ := by
  have hquot :
      (QuotientAddGroup.mk (Quotient.out (γ - δ)) : data.Group) =
        QuotientAddGroup.mk (Quotient.out γ - Quotient.out δ) := by
    simp [Quotient.out_eq γ, Quotient.out_eq δ]
  filter_upwards
    [(data.quotient_eq_iff_eventually_lift_eq
      (w := Quotient.out (γ - δ))
      (v := Quotient.out γ - Quotient.out δ)).mp hquot] with n hn
  change data.finiteLiftHom n (Quotient.out (γ - δ)) =
    data.finiteLiftHom n (Quotient.out γ) - data.finiteLiftHom n (Quotient.out δ)
  rw [hn]
  exact (data.finiteLiftHom n).map_sub _ _

lemma finiteLift_sum_eventually_eq
    (data : F.StableSubseqData labelFreq)
    {ι : Type*} (s : Finset ι) (f : ι → data.Group) :
    ∀ᶠ n in atTop,
      data.finiteLift n (∑ i ∈ s, f i) =
        ∑ i ∈ s, data.finiteLift n (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · filter_upwards [data.finiteLift_zero_eventually_eq_zero] with n hzero
    simpa using hzero
  · intro a s ha ih
    filter_upwards
      [ih, data.finiteLift_add_eventually_eq (f a) (∑ i ∈ s, f i)] with n hsum hadd
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, hsum]

/-- Nonzero quotient elements have nonzero finite lifts eventually. -/
lemma finiteLift_eventually_ne_zero
    (data : F.StableSubseqData labelFreq)
    {γ : data.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ 0 := by
  rcases data.finiteLift_eventually_stable (Quotient.out γ) with hzero | hnonzero
  · have hγ0 : γ = 0 := by
      have hmk :
          (QuotientAddGroup.mk (Quotient.out γ) : data.Group) = 0 :=
        (data.quotient_eq_zero_iff_eventually_lift_eq_zero
          (w := Quotient.out γ)).mpr (by
            simpa [finiteLiftHom_apply] using hzero)
      simpa [Quotient.out_eq γ] using hmk
    exact (hγ hγ0).elim
  · simpa [finiteLift, finiteLiftHom_apply] using hnonzero

/-- Distinct quotient elements have distinct finite lifts eventually. -/
lemma finiteLift_eventually_ne_of_ne
    (data : F.StableSubseqData labelFreq)
    {γ δ : data.Group} (hγδ : γ ≠ δ) :
    ∀ᶠ n in atTop, data.finiteLift n γ ≠ data.finiteLift n δ := by
  have hsub : γ - δ ≠ 0 := sub_ne_zero.mpr hγδ
  filter_upwards
    [data.finiteLift_eventually_ne_zero hsub,
      data.finiteLift_sub_eventually_eq γ δ] with n hn hsubeq heq
  exact hn (by simpa [heq] using hsubeq)

/-- The finite lift is eventually injective on any fixed finite subset of the
extraction quotient. -/
lemma finiteLift_eventually_injOn_finset
    (data : F.StableSubseqData labelFreq) (Q : Finset data.Group) :
    ∀ᶠ n in atTop,
      Set.InjOn (fun γ => data.finiteLift n γ) (Q : Set data.Group) := by
  classical
  have hpairs :
      ∀ᶠ n in atTop, ∀ pair ∈ Q.product Q,
        pair.1 ≠ pair.2 →
          data.finiteLift n pair.1 ≠ data.finiteLift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hmem
    by_cases hp : pair.1 = pair.2
    · exact Eventually.of_forall fun _ hne => (hne hp).elim
    · exact (data.finiteLift_eventually_ne_of_ne hp).mono
        (fun _ hn _hne => hn)
  filter_upwards [hpairs] with n hn γ hγ δ hδ heq
  by_contra hne
  have hpair : (γ, δ) ∈ Q.product Q := Finset.mem_product.mpr ⟨hγ, hδ⟩
  exact (hn (γ, δ) hpair hne) heq

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/TorsionFree.lean
    ============================================================= -/

/-
Erdős Problem 42 — torsion-freeness of the compact-Cayley extraction quotient.

Finite lifts land in cyclic groups of prime order tending to infinity along the
stable subsequence.  A fixed nonzero scalar cannot create persistent torsion in
those cyclic groups, hence the eventual-kernel quotient is torsion-free.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

lemma eventually_prime_gt
    (data : F.StableSubseqData labelFreq) (q : ℕ) :
    ∀ᶠ n in atTop, q < F.p (data.φ n) := by
  rw [Filter.eventually_atTop]
  refine ⟨q + 1, ?_⟩
  intro n hn
  have hq_lt_n : q < n :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self q) hn
  have hn_le_φn : n ≤ data.φ n := data.strictMono_φ.le_apply
  exact lt_trans (lt_of_lt_of_le hq_lt_n hn_le_φn)
    (F.p_gt (data.φ n))

lemma zmod_nsmul_eq_zero_iff_of_prime_not_dvd
    {p q : ℕ} [Fact p.Prime] (hnot : ¬ p ∣ q) (x : ZMod p) :
    q • x = 0 ↔ x = 0 := by
  have hunit : IsUnit (q : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnot).symm
  constructor
  · intro hx
    have hxmul : (q : ZMod p) * x = (q : ZMod p) * 0 := by
      simpa [nsmul_eq_mul] using hx
    exact hunit.mul_left_cancel hxmul
  · intro hx
    simp [hx]

lemma quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    (q : ℕ) {w : ExtractionFreeGroup} :
    q • (QuotientAddGroup.mk w : data.Group) = 0 ↔
      ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0 := by
  rw [← QuotientAddGroup.mk_nsmul
    ((data.seq).eventualKernel data.subseqLabelFreq) w q,
    data.quotient_eq_zero_iff_eventually_lift_eq_zero]
  simp [AddMonoidHom.map_nsmul]

lemma finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
    (data : F.StableSubseqData labelFreq)
    {q : ℕ} (hq : q ≠ 0) {w : ExtractionFreeGroup}
    (h : ∀ᶠ n in atTop, q • data.finiteLiftHom n w = 0) :
    ∀ᶠ n in atTop, data.finiteLiftHom n w = 0 := by
  filter_upwards [h, data.eventually_prime_gt q] with n hn hgt
  have : Fact (F.p (data.φ n)).Prime := ⟨F.prime (data.φ n)⟩
  have hnot : ¬ F.p (data.φ n) ∣ q :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hq) hgt
  exact (zmod_nsmul_eq_zero_iff_of_prime_not_dvd hnot
    (data.finiteLiftHom n w)).mp hn

/-- The stable compact-Cayley extraction quotient is torsion-free. -/
theorem group_isAddTorsionFree
    (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group where
  nsmul_right_injective := by
    intro q hq x y hxy
    induction x using QuotientAddGroup.induction_on with
    | H w =>
      induction y using QuotientAddGroup.induction_on with
      | H v =>
        have hsub_q :
            q • (QuotientAddGroup.mk (w - v) : data.Group) = 0 := by
          rw [QuotientAddGroup.mk_sub]
          simp [nsmul_sub, hxy]
        have hlift_q :
            ∀ᶠ n in atTop, q • data.finiteLiftHom n (w - v) = 0 :=
          (data.quotient_nsmul_eq_zero_iff_eventually_lift_nsmul_eq_zero
            q).mp hsub_q
        have hlift :
            ∀ᶠ n in atTop, data.finiteLiftHom n (w - v) = 0 :=
          data.finiteLiftHom_eventually_eq_zero_of_eventually_nsmul_eq_zero
            hq hlift_q
        have hsub :
            (QuotientAddGroup.mk (w - v) : data.Group) = 0 :=
          (data.quotient_eq_zero_iff_eventually_lift_eq_zero).mpr hlift
        rw [QuotientAddGroup.mk_sub] at hsub
        exact sub_eq_zero.mp hsub

instance (data : F.StableSubseqData labelFreq) :
    IsAddTorsionFree data.Group :=
  data.group_isAddTorsionFree

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CoeffLimit.lean
    ============================================================= -/

/-
Erdős Problem 42 — quotient coefficient limits and large-spectrum cover.

This file pushes the formal-word coefficient limits from stable extraction data
to chosen representatives of quotient frequencies.  It also records the key
large-spectrum covering consequence of the non-nested labels.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped BigOperators Topology

noncomputable section

namespace FourierSeq.StableSubseqData

variable {F : FourierSeq} {labelFreq : LargeLabel → ∀ n, ZMod (F.p n)}

/-- Coefficient limit attached to a quotient frequency, using its chosen
representative. -/
noncomputable def coeff
    (data : F.StableSubseqData labelFreq) (γ : data.Group) : ℂ :=
  data.coeffLimit (Quotient.out γ)

lemma coeff_tendsto
    (data : F.StableSubseqData labelFreq) (γ : data.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (F.p (data.φ n)) := ⟨(F.prime (data.φ n)).ne_zero⟩;
        F.coeff (data.φ n) (data.finiteLift n γ))
      atTop (𝓝 (data.coeff γ)) := by
  simpa [coeff, finiteLift, finiteLiftHom_apply] using
    data.coeffLimit_tendsto (Quotient.out γ)

/-- Quotient generator associated to a large-spectrum label. -/
noncomputable def generator
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    data.Group :=
  QuotientAddGroup.mk (FreeAbelianGroup.of label)

/-- The finite set of quotient frequencies representing the `q`-large
spectrum, plus zero. -/
noncomputable def largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+) :
    Finset data.Group :=
  ((Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).image
      (fun k => data.generator (⟨q, k⟩ : LargeLabel))) ∪ {0}

lemma generator_mem_largeSpectrumGenerators
    (data : F.StableSubseqData labelFreq) (q : ℕ+)
    (k : Fin ((q : ℕ) ^ 2 + 1)) :
    data.generator (⟨q, k⟩ : LargeLabel) ∈
      data.largeSpectrumGenerators q := by
  classical
  unfold largeSpectrumGenerators
  exact Finset.mem_union.mpr <|
    Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)

/-- Label generators have their labelled finite frequency as finite lift,
eventually. -/
lemma finiteLift_generator_eventually_eq
    (data : F.StableSubseqData labelFreq) (label : LargeLabel) :
    ∀ᶠ n in atTop,
      data.finiteLift n (data.generator label) =
        labelFreq label (data.φ n) := by
  filter_upwards
    [data.finiteLift_mk_eventually_eq (FreeAbelianGroup.of label)] with n hn
  simpa [generator, finiteLiftHom_apply, FourierSeq.wordLift,
    FourierSeq.wordLiftHom_apply_of] using hn

/-- If `labelFreq` covers every finite large spectrum before extraction, then
the quotient generators cover every finite large spectrum along the stable
subsequence. -/
lemma eventually_largeSpectrum_covered
    (data : F.StableSubseqData labelFreq)
    (hcover :
      ∀ q n r, r ∈ F.largeSpectrum q n →
        ∃ k : Fin ((q : ℕ) ^ 2 + 1),
          labelFreq ⟨q, k⟩ n = r)
    (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (F.p (data.φ n)),
        ((q : ℝ)⁻¹ : ℝ) < ‖F.coeff (data.φ n) r‖ →
          ∃ γ ∈ data.largeSpectrumGenerators q,
            data.finiteLift n γ = r := by
  classical
  have hlabels' :
      ∀ᶠ n in atTop,
        ∀ k ∈ (Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    rw [(Finset.univ : Finset (Fin ((q : ℕ) ^ 2 + 1))).eventually_all]
    intro k _hk
    exact data.finiteLift_generator_eventually_eq (⟨q, k⟩ : LargeLabel)
  have hlabels :
      ∀ᶠ n in atTop,
        ∀ k : Fin ((q : ℕ) ^ 2 + 1),
          data.finiteLift n (data.generator (⟨q, k⟩ : LargeLabel)) =
            labelFreq ⟨q, k⟩ (data.φ n) := by
    filter_upwards [hlabels'] with n hn k
    exact hn k (Finset.mem_univ k)
  filter_upwards [hlabels] with n hn r hr
  have hrmem : r ∈ F.largeSpectrum q (data.φ n) :=
    FourierSeq.mem_largeSpectrum.mpr hr
  rcases hcover q (data.φ n) r hrmem with ⟨k, hk⟩
  refine ⟨data.generator (⟨q, k⟩ : LargeLabel),
    data.generator_mem_largeSpectrumGenerators q k, ?_⟩
  exact (hn k).trans hk

end FourierSeq.StableSubseqData

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CayleyExtraction.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley extraction specialized to counterexamples.

This file connects the generic Fourier extraction sequence to the concrete
counterexample sets `T_n`.  The resulting coefficient facts are the finite
hypotheses that later define the compact limit kernel.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

/-- Stable Fourier extraction package attached to a compact-Cayley
counterexample sequence. -/
structure CayleyExtraction {ℓ : ℕ} {η : ℝ}
    (S : CayleyCounterSeq ℓ η) where
  data :
    (S.toFourierSeq).StableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The discrete extraction quotient. -/
abbrev Group (E : CayleyExtraction S) : Type :=
  E.data.Group

instance (E : CayleyExtraction S) : Countable E.Group :=
  inferInstance

instance (E : CayleyExtraction S) : IsAddTorsionFree E.Group :=
  inferInstance

/-- The selected index in the original counterexample sequence. -/
def φ (E : CayleyExtraction S) : ℕ → ℕ :=
  E.data.φ

lemma strictMono_φ (E : CayleyExtraction S) :
    StrictMono E.φ :=
  E.data.strictMono_φ

/-- Finite lift of an extraction quotient frequency to the selected cyclic
group. -/
noncomputable def lift (E : CayleyExtraction S)
    (n : ℕ) (γ : E.Group) :
    ZMod (S.p (E.φ n)) :=
  E.data.finiteLift n γ

/-- Coefficient limit attached to a quotient frequency. -/
noncomputable def coeff (E : CayleyExtraction S) (γ : E.Group) : ℂ :=
  E.data.coeff γ

lemma coeff_tendsto (E : CayleyExtraction S) (γ : E.Group) :
    Tendsto
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))
      atTop (𝓝 (E.coeff γ)) := by
  simpa [coeff, lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using E.data.coeff_tendsto γ

/-- Canonical labels cover all finite large spectra along the extracted
subsequence. -/
lemma eventually_largeSpectrum_covered
    (E : CayleyExtraction S) (q : ℕ+) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        ((q : ℝ)⁻¹ : ℝ) <
            ‖(letI : NeZero (S.p (E.φ n)) :=
                ⟨(S.prime (E.φ n)).ne_zero⟩;
              normalizedDftCoeff (S.T (E.φ n)) r)‖ →
          ∃ γ ∈ E.data.largeSpectrumGenerators q,
            E.lift n γ = r := by
  have hcover :
      ∀ q n r,
        r ∈ (S.toFourierSeq).largeSpectrum q n →
          ∃ k : Fin ((q : ℕ) ^ 2 + 1),
            (S.toFourierSeq).largeSpectrumLabelFreq ⟨q, k⟩ n = r := by
    intro q n r hr
    exact (S.toFourierSeq).exists_largeSpectrumLabelFreq_eq_of_mem q n hr
  simpa [lift, φ, CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
    normalizedDftCoeff] using
      E.data.eventually_largeSpectrum_covered hcover q

lemma coeff_im_eq_zero (E : CayleyExtraction S) (γ : E.Group) :
    (E.coeff γ).im = 0 := by
  have hlim :=
    Complex.continuous_im.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have him :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).im) = 0 :=
    Filter.Eventually.of_forall (fun n => by
      let : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      exact normalizedDftCoeff_im_eq_zero_of_symmetric
        (S.T_sym (E.φ n)) (E.lift n γ))
  have hzero :
      Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 (E.coeff γ).im) :=
    Filter.Tendsto.congr' him hlim
  exact tendsto_nhds_unique hzero tendsto_const_nhds

lemma coeff_neg_eq (E : CayleyExtraction S) (γ : E.Group) :
    E.coeff (-γ) = E.coeff γ := by
  have hneg_tendsto := E.coeff_tendsto (-γ)
  have hpos_tendsto := E.coeff_tendsto γ
  have heq :
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n (-γ))) =ᶠ[atTop]
      (fun n =>
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [lift, lift, hneg]
    exact normalizedDftCoeff_neg_eq_of_symmetric (S.T_sym (E.φ n)) (E.lift n γ)
  exact tendsto_nhds_unique (hneg_tendsto.congr' heq) hpos_tendsto

lemma coeff_nonpos_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    (E.coeff γ).re ≤ 0 := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff γ) |>.comp (E.coeff_tendsto γ)
  have heps :
      Tendsto (fun n => S.eps (E.φ n)) atTop (𝓝 0) :=
    S.eps_tendsto_zero.comp E.strictMono_φ.tendsto_atTop
  have hupper :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          (normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)).re) ≤
          S.eps (E.φ n) := by
    filter_upwards [E.data.finiteLift_eventually_ne_zero hγ] with n hn
    let : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    exact S.T_fourier_upper (E.φ n) (E.lift n γ) hn
  exact le_of_tendsto_of_tendsto hlim heps hupper

lemma coeff_zero_ge_eta (E : CayleyExtraction S) :
    η ≤ (E.coeff 0).re := by
  have hlim :=
    Complex.continuous_re.tendsto (E.coeff (0 : E.Group)) |>.comp
      (E.coeff_tendsto (0 : E.Group))
  have hdens :
      ∀ᶠ n in atTop,
        η ≤
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            (normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) := by
    filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
    let : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    have hp_pos : 0 < (S.p (E.φ n) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (S.prime (E.φ n)).ne_zero
    have hη_div :
        η ≤ ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) :=
      (le_div_iff₀ hp_pos).mpr (S.T_density (E.φ n))
    have hlift : E.lift n (0 : E.Group) = (0 : ZMod (S.p (E.φ n))) := by
      change E.data.finiteLift n (0 : E.data.Group) = 0
      exact hn
    have hcoeff_re :
        ((normalizedDftCoeff (S.T (E.φ n)) (E.lift n 0)).re) =
          ((S.T (E.φ n)).card : ℝ) / (S.p (E.φ n) : ℝ) := by
      rw [hlift]
      rw [normalizedDftCoeff_zero_eq_card_div]
      simp
    rw [hcoeff_re]
    exact hη_div
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hdens

end CayleyExtraction

/-- Existence of compact-Cayley stable extraction data for a counterexample
sequence. -/
theorem exists_cayleyExtraction
    {ℓ : ℕ} {η : ℝ} (S : CayleyCounterSeq ℓ η) :
    ∃ _E : CayleyExtraction S, True := by
  classical
  rcases (S.toFourierSeq).exists_stableSubseqData
      (S.toFourierSeq.largeSpectrumLabelFreq) with
    ⟨data, _⟩
  exact ⟨⟨data⟩, trivial⟩

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CompactDual.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact dual attached to compact-Cayley extraction.

The extraction quotient is a countable discrete torsion-free abelian group.
This file builds its Pontryagin dual, then wraps it additively so the compact
endpoint can use additive notation and Haar probability measure.
-/

namespace Erdos42.CompactCayley

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

instance groupTopologicalSpace (E : CayleyExtraction S) :
    TopologicalSpace E.Group :=
  ⊥

instance groupDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.Group :=
  ⟨rfl⟩

/-- Multiplicative version of the extraction quotient, for Mathlib's
`PontryaginDual` API. -/
abbrev DualDomain (E : CayleyExtraction S) : Type :=
  Multiplicative E.Group

/-- Compact Pontryagin dual of the extraction quotient. -/
abbrev CompactDual (E : CayleyExtraction S) : Type :=
  PontryaginDual E.DualDomain

/-- Additive wrapper around the compact extraction dual. -/
abbrev CompactAddDual (E : CayleyExtraction S) : Type :=
  Additive E.CompactDual

instance dualDomainCountable (E : CayleyExtraction S) :
    Countable E.DualDomain :=
  Countable.of_equiv E.Group Multiplicative.ofAdd

instance dualDomainDiscreteTopology (E : CayleyExtraction S) :
    DiscreteTopology E.DualDomain :=
  inferInstance

instance dualDomainSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.DualDomain := by
  let : Countable E.DualDomain := dualDomainCountable E
  let : DiscreteTopology E.DualDomain := dualDomainDiscreteTopology E
  infer_instance

instance compactDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactDual := by
  dsimp [CompactDual, PontryaginDual]
  exact (ContinuousMonoidHom.isInducing_toContinuousMap
    E.DualDomain Circle).secondCountableTopology

/-- Identity homeomorphism from the multiplicative compact dual to its
additive wrapper. -/
def compactDualAdditiveHomeomorph (E : CayleyExtraction S) :
    E.CompactDual ≃ₜ E.CompactAddDual where
  toEquiv := Additive.ofMul
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

theorem compactAddDual_t2Space (E : CayleyExtraction S) :
    T2Space E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).t2Space

theorem compactAddDual_compactSpace (E : CayleyExtraction S) :
    CompactSpace E.CompactAddDual :=
  inferInstance

theorem compactAddDual_isTopologicalAddGroup (E : CayleyExtraction S) :
    IsTopologicalAddGroup E.CompactAddDual :=
  inferInstance

instance compactAddDualSecondCountableTopology (E : CayleyExtraction S) :
    SecondCountableTopology E.CompactAddDual :=
  (E.compactDualAdditiveHomeomorph).symm.secondCountableTopology

instance compactAddDualMeasurableSpace (E : CayleyExtraction S) :
    MeasurableSpace E.CompactAddDual :=
  borel E.CompactAddDual

instance compactAddDualBorelSpace (E : CayleyExtraction S) :
    BorelSpace E.CompactAddDual :=
  ⟨rfl⟩

instance compactAddDualMeasurableAdd₂ (E : CayleyExtraction S) :
    MeasurableAdd₂ E.CompactAddDual where
  measurable_add := continuous_add.measurable

instance compactAddDualMeasurableNeg (E : CayleyExtraction S) :
    MeasurableNeg E.CompactAddDual where
  measurable_neg := continuous_neg.measurable

instance compactAddDualMeasurableSub₂ (E : CayleyExtraction S) :
    MeasurableSub₂ E.CompactAddDual where
  measurable_sub := continuous_sub.measurable

/-- Normalized additive Haar probability measure on the compact additive dual. -/
noncomputable def haar (E : CayleyExtraction S) :
    MeasureTheory.Measure E.CompactAddDual :=
  MeasureTheory.Measure.addHaarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)

instance haar_isAddHaarMeasure (E : CayleyExtraction S) :
    (E.haar).IsAddHaarMeasure := by
  unfold haar
  infer_instance

instance haar_isOpenPosMeasure (E : CayleyExtraction S) :
    (E.haar).IsOpenPosMeasure :=
  inferInstance

instance haar_isProbabilityMeasure (E : CayleyExtraction S) :
    MeasureTheory.IsProbabilityMeasure E.haar where
  measure_univ := by
    unfold haar
    simpa using
      (MeasureTheory.Measure.addHaarMeasure_self
        (K₀ := (⊤ : TopologicalSpace.PositiveCompacts E.CompactAddDual)))

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Characters.lean
    ============================================================= -/

/-
Erdős Problem 42 — characters on the compact-Cayley compact dual.
-/

namespace Erdos42.CompactCayley

open MeasureTheory
open scoped ComplexConjugate Topology

noncomputable section

/-- The rational character module target `ℚ / ℤ`, embedded in the usual unit
circle. -/
noncomputable def ratAddCircleToCircleAdditive :
    AddCircle (1 : ℚ) →+ Additive Circle := by
  let f : ℚ →+ Additive Circle :=
    { toFun := fun q =>
        Additive.ofMul
          (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))))
      map_zero' := by
        simp
      map_add' := by
        intro a b
        ext
        simp [Rat.cast_add, AddCircle.toCircle_add] }
  refine QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : ℚ)) f ?_
  intro x hx
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  change
    Additive.ofMul
        (AddCircle.toCircle
          ((((k • (1 : ℚ) : ℚ) : ℝ) : AddCircle (1 : ℝ)))) = 0
  rw [ofMul_eq_zero]
  have hzero :
      (((k : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  simpa using congrArg (fun y : AddCircle (1 : ℝ) => AddCircle.toCircle y) hzero

lemma ratAddCircleToCircleAdditive_eq_zero
    {x : AddCircle (1 : ℚ)}
    (hx : ratAddCircleToCircleAdditive x = 0) :
    x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
      change ratAddCircleToCircleAdditive ((q : AddCircle (1 : ℚ))) = 0 at hx
      have hcircle :
          AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ))) = 1 := by
        have hx' :
            Additive.ofMul
              (AddCircle.toCircle (((q : ℝ) : AddCircle (1 : ℝ)))) = 0 := by
          simpa [ratAddCircleToCircleAdditive] using hx
        exact ofMul_eq_zero.mp hx'
      have hreal :
          (((q : ℝ) : AddCircle (1 : ℝ))) = 0 :=
        (AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero)
          (by simpa using hcircle)
      rw [AddCircle.coe_eq_zero_iff] at hreal ⊢
      rcases hreal with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Rat.cast_injective (α := ℝ)
      simpa using hk

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Evaluation of a compact-dual character at an extraction quotient
frequency, viewed in `ℂ`. -/
noncomputable def characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) : ℂ :=
  (z (Multiplicative.ofAdd γ) : ℂ)

/-- Character evaluation on the additive compact-dual wrapper. -/
noncomputable def addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) : ℂ :=
  E.characterValue z.toMul γ

@[simp]
lemma characterValue_zero
    (E : CayleyExtraction S) (z : E.CompactDual) :
    E.characterValue z (0 : E.Group) = 1 := by
  simp [characterValue]

@[simp]
lemma characterValue_add
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ + δ) =
      E.characterValue z γ * E.characterValue z δ := by
  simp [characterValue]

@[simp]
lemma characterValue_neg
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z (-γ) = (E.characterValue z γ)⁻¹ := by
  simp [characterValue]

@[simp]
lemma star_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    star (E.characterValue z γ) = E.characterValue z (-γ) := by
  unfold characterValue
  rw [show star (↑(z (Multiplicative.ofAdd γ)) : ℂ) =
      conj (↑(z (Multiplicative.ofAdd γ)) : ℂ) by rfl]
  rw [← Circle.coe_inv_eq_conj]
  simp

lemma characterValue_sub
    (E : CayleyExtraction S) (z : E.CompactDual)
    (γ δ : E.Group) :
    E.characterValue z (γ - δ) =
      E.characterValue z γ * star (E.characterValue z δ) := by
  rw [sub_eq_add_neg, characterValue_add, star_characterValue]

@[simp]
lemma characterValue_one_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.characterValue (1 : E.CompactDual) γ = 1 := by
  rfl

@[simp]
lemma characterValue_mul_point
    (E : CayleyExtraction S) (z w : E.CompactDual) (γ : E.Group) :
    E.characterValue (z * w) γ =
      E.characterValue z γ * E.characterValue w γ := by
  rfl

@[simp]
lemma characterValue_inv_point
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    E.characterValue z⁻¹ γ = (E.characterValue z γ)⁻¹ := by
  rfl

@[simp]
lemma addCharacterValue_zero
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.addCharacterValue z (0 : E.Group) = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ + δ) =
      E.addCharacterValue z γ * E.addCharacterValue z δ := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_neg
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue z (-γ) = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma star_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    star (E.addCharacterValue z γ) = E.addCharacterValue z (-γ) := by
  simp [addCharacterValue, star_characterValue]

lemma addCharacterValue_sub
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ δ : E.Group) :
    E.addCharacterValue z (γ - δ) =
      E.addCharacterValue z γ * star (E.addCharacterValue z δ) := by
  simpa [addCharacterValue] using E.characterValue_sub z.toMul γ δ

@[simp]
lemma addCharacterValue_zero_point
    (E : CayleyExtraction S) (γ : E.Group) :
    E.addCharacterValue (0 : E.CompactAddDual) γ = 1 := by
  simp [addCharacterValue]

@[simp]
lemma addCharacterValue_add_point
    (E : CayleyExtraction S) (z w : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (z + w) γ =
      E.addCharacterValue z γ * E.addCharacterValue w γ := by
  simp [addCharacterValue]

lemma addCharacterValue_nsmul_frequency
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue z (n • γ) =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add, ih, pow_succ]

lemma addCharacterValue_nsmul_point
    (E : CayleyExtraction S) (z : E.CompactAddDual)
    (γ : E.Group) (n : ℕ) :
    E.addCharacterValue (n • z) γ =
      (E.addCharacterValue z γ) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [succ_nsmul, E.addCharacterValue_add_point, ih, pow_succ]

@[simp]
lemma addCharacterValue_neg_point
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    E.addCharacterValue (-z) γ = (E.addCharacterValue z γ)⁻¹ := by
  simp [addCharacterValue]

@[simp]
lemma norm_characterValue
    (E : CayleyExtraction S) (z : E.CompactDual) (γ : E.Group) :
    ‖E.characterValue z γ‖ = 1 :=
  Circle.norm_coe _

@[simp]
lemma norm_addCharacterValue
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    ‖E.addCharacterValue z γ‖ = 1 := by
  simp [addCharacterValue]

lemma characterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactDual => E.characterValue z γ) := by
  change Continuous (fun z : E.DualDomain →ₜ* Circle =>
    ((z.toContinuousMap (Multiplicative.ofAdd γ) : Circle) : ℂ))
  exact
    (continuous_subtype_val.comp
      ((continuous_eval_const (F := C(E.DualDomain, Circle))
        (Multiplicative.ofAdd γ)).comp
          (ContinuousMonoidHom.isInducing_toContinuousMap
            E.DualDomain Circle).continuous))

lemma addCharacterValue_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.addCharacterValue z γ) := by
  change Continuous (fun z : E.CompactAddDual => E.characterValue z.toMul γ)
  exact
    (E.characterValue_continuous γ).comp
      (E.compactDualAdditiveHomeomorph.symm.continuous)

@[simp]
lemma integral_addCharacterValue_zero
    (E : CayleyExtraction S) :
    ∫ z : E.CompactAddDual,
        E.addCharacterValue z (0 : E.Group) ∂E.haar = 1 := by
  simp

/-- Haar orthogonality for a character once a point where it is nontrivial has
been supplied.  The separate Pontryagin-dual separation theorem should provide
this witness for every nonzero extraction frequency. -/
lemma integral_addCharacterValue_eq_zero_of_exists_ne_one
    (E : CayleyExtraction S) (γ : E.Group)
    (hne : ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar = 0 := by
  classical
  rcases hne with ⟨y, hy⟩
  let I : ℂ :=
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar
  have htrans :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) = I := by
    simpa [I] using
      (integral_add_left_eq_self
        (μ := E.haar)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ) y)
  have hleft :
      (∫ z : E.CompactAddDual,
          E.addCharacterValue (y + z) γ ∂E.haar) =
        E.addCharacterValue y γ * I := by
    simp_rw [E.addCharacterValue_add_point y]
    simpa [I] using
      (integral_const_mul (μ := E.haar) (E.addCharacterValue y γ)
        (fun z : E.CompactAddDual => E.addCharacterValue z γ))
  have hscalar : E.addCharacterValue y γ * I = I := by
    rw [← hleft, htrans]
  have hzero : (E.addCharacterValue y γ - 1) * I = 0 := by
    calc
      (E.addCharacterValue y γ - 1) * I =
          E.addCharacterValue y γ * I - I := by ring
      _ = I - I := by rw [hscalar]
      _ = 0 := by ring
  have hfactor : E.addCharacterValue y γ - 1 ≠ 0 := sub_ne_zero.mpr hy
  exact (mul_eq_zero.mp hzero).resolve_left hfactor

lemma integral_addCharacterValue_eq_if_of_separating
    (E : CayleyExtraction S)
    (hsep :
      ∀ γ : E.Group, γ ≠ 0 →
        ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1)
    (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 := by
  by_cases hγ : γ = 0
  · subst γ
    simp
  · simp [hγ, E.integral_addCharacterValue_eq_zero_of_exists_ne_one γ (hsep γ hγ)]

lemma exists_dual_point_ne_one
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∃ y : E.CompactAddDual, E.addCharacterValue y γ ≠ 1 := by
  classical
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero
      (A := E.Group) (a := γ) hγ
  let ψ : E.Group →+ Additive Circle :=
    ratAddCircleToCircleAdditive.comp c
  have hψ : ψ γ ≠ 0 := by
    intro hzero
    exact hc (ratAddCircleToCircleAdditive_eq_zero hzero)
  let mψ : E.DualDomain →* Circle :=
    AddMonoidHom.toMultiplicativeLeft ψ
  let z : E.CompactDual :=
    { toMonoidHom := mψ
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨Additive.ofMul z, ?_⟩
  intro htriv
  have hcoe :
      ((mψ (Multiplicative.ofAdd γ) : Circle) : ℂ) = 1 := by
    change ((z (Multiplicative.ofAdd γ) : Circle) : ℂ) = 1
    simpa [addCharacterValue, characterValue] using htriv
  have hmψ : mψ (Multiplicative.ofAdd γ) = 1 := by
    exact Subtype.ext hcoe
  have hcircle : (ψ γ).toMul = 1 := by
    simpa [mψ, AddMonoidHom.coe_toMultiplicativeLeft] using hmψ
  exact hψ (toMul_eq_one.mp hcircle)

lemma integral_addCharacterValue
    (E : CayleyExtraction S) (γ : E.Group) :
    ∫ z : E.CompactAddDual, E.addCharacterValue z γ ∂E.haar =
      if γ = 0 then 1 else 0 :=
  E.integral_addCharacterValue_eq_if_of_separating
    (fun _ hγ => E.exists_dual_point_ne_one hγ) γ

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/TrigPolynomial.lean
    ============================================================= -/

/-
Erdős Problem 42 — trigonometric polynomials for compact-Cayley extraction.

This is the finite-support Fourier-polynomial interface on the extraction
quotient, together with finite cyclic lifts and the zero-frequency finite
average convergence that follows from relation-stable quotient lifts.
-/

namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finitely supported Fourier polynomials on the extraction quotient. -/
abbrev TrigPoly (E : CayleyExtraction S) : Type :=
  E.Group →₀ ℂ

/-- Compact-dual evaluation of an extraction trigonometric polynomial. -/
noncomputable def TrigPoly.eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactDual) : ℂ :=
  P.sum fun γ c => c * E.characterValue z γ

/-- Additive-wrapper compact-dual evaluation. -/
noncomputable def TrigPoly.evalAdd
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) : ℂ :=
  P.sum fun γ c => c * E.addCharacterValue z γ

/-- Finite cyclic lift of a trigonometric polynomial. -/
noncomputable def TrigPoly.evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c => c * ZMod.stdAddChar (-(E.lift n γ * x))

/-- Normalized finite average of a lifted trigonometric polynomial. -/
noncomputable def TrigPoly.finiteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => P.evalFinite n x

/-- Finite average of a lifted trigonometric polynomial against the Cayley-set
indicator. -/
noncomputable def TrigPoly.indicatorWeightedFiniteAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    indicatorC (S.T (E.φ n)) x * P.evalFinite n x

/-- Abstract compact average, represented algebraically by the zero-frequency
coefficient. -/
noncomputable def TrigPoly.compactAverage
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P (0 : E.Group)

/-- Compact-limit coefficient functional obtained by pairing a trigonometric
polynomial with the extracted Cayley Fourier coefficient limits. -/
noncomputable def TrigPoly.indicatorCoeffFunctional
    {E : CayleyExtraction S} (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * E.coeff γ

lemma TrigPoly.evalAdd_eq_eval
    {E : CayleyExtraction S} (P : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z = TrigPoly.eval P z.toMul := by
  rfl

lemma TrigPoly.eval_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactDual) :
    TrigPoly.eval (P + Q) z =
      TrigPoly.eval P z + TrigPoly.eval Q z := by
  unfold TrigPoly.eval
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.characterValue z γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.evalAdd_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (z : E.CompactAddDual) :
    TrigPoly.evalAdd (P + Q) z =
      TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z := by
  simpa [TrigPoly.evalAdd_eq_eval] using
    TrigPoly.eval_add P Q z.toMul

@[simp]
lemma TrigPoly.eval_zero
    {E : CayleyExtraction S} (z : E.CompactDual) :
    TrigPoly.eval (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_zero
    {E : CayleyExtraction S} (z : E.CompactAddDual) :
    TrigPoly.evalAdd (0 : E.TrigPoly) z = 0 := by
  simp [TrigPoly.evalAdd_eq_eval]

@[simp]
lemma TrigPoly.eval_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactDual) :
    TrigPoly.eval (Finsupp.single γ c : E.TrigPoly) z =
      c * E.characterValue z γ := by
  simp [TrigPoly.eval]

@[simp]
lemma TrigPoly.evalAdd_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z =
      c * E.addCharacterValue z γ := by
  simp [TrigPoly.evalAdd]

@[simp]
lemma TrigPoly.eval_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactDual) :
    TrigPoly.eval
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

@[simp]
lemma TrigPoly.evalAdd_single_zero
    {E : CayleyExtraction S} (c : ℂ) (z : E.CompactAddDual) :
    TrigPoly.evalAdd
        (Finsupp.single (0 : E.Group) c : E.TrigPoly) z = c := by
  simp

lemma TrigPoly.continuous_evalAdd
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Continuous (fun z : E.CompactAddDual => TrigPoly.evalAdd P z) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simpa using (continuous_const :
      Continuous (fun _ : E.CompactAddDual => (0 : ℂ)))
  · intro P Q hP hQ
    rw [show
        (fun z : E.CompactAddDual => TrigPoly.evalAdd (P + Q) z) =
          fun z => TrigPoly.evalAdd P z + TrigPoly.evalAdd Q z by
        funext z
        exact TrigPoly.evalAdd_add P Q z]
    exact hP.add hQ
  · intro γ c
    rw [show
        (fun z : E.CompactAddDual =>
            TrigPoly.evalAdd (Finsupp.single γ c : E.TrigPoly) z) =
          fun z => c * E.addCharacterValue z γ by
        funext z
        exact TrigPoly.evalAdd_single γ c z]
    exact continuous_const.mul (E.addCharacterValue_continuous γ)

@[simp]
lemma TrigPoly.evalFinite_zero
    {E : CayleyExtraction S} (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (0 : E.TrigPoly) n x = 0 := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  simp [TrigPoly.evalFinite]

@[simp]
lemma TrigPoly.evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * ZMod.stdAddChar (-(E.lift n γ * x))) := by
  simp [TrigPoly.evalFinite]

lemma TrigPoly.evalFinite_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (P + Q) n x =
      TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  classical
  unfold TrigPoly.evalFinite
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * ZMod.stdAddChar (-(E.lift n γ * x))
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma TrigPoly.finiteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.finiteAverage (P + Q) n =
      TrigPoly.finiteAverage P n + TrigPoly.finiteAverage Q n := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.finiteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x) by
        funext x
        exact TrigPoly.evalFinite_add P Q n x]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma TrigPoly.indicatorWeightedFiniteAverage_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage (P + Q) n =
      TrigPoly.indicatorWeightedFiniteAverage P n +
        TrigPoly.indicatorWeightedFiniteAverage Q n := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (P + Q) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite P n x +
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite Q n x) by
        funext x
        rw [TrigPoly.evalFinite_add]
        ring]
  unfold avgZMod
  rw [Finset.sum_add_distrib, mul_add]

lemma avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero
    {p : ℕ} [Fact p.Prime] [NeZero p] {r : ZMod p} (hr : r ≠ 0) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) = 0 := by
  unfold avgZMod
  rw [show (∑ x : ZMod p, ZMod.stdAddChar (-(r * x))) = 0 by
    simpa [mul_comm] using
      sum_stdAddChar_neg_mul_eq_zero_of_ne_zero (p := p) (r := r) hr]
  simp

lemma avgZMod_stdAddChar_neg_mul_eq_ite
    {p : ℕ} [Fact p.Prime] [NeZero p] (r : ZMod p) :
    avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(r * x))) =
      if r = 0 then 1 else 0 := by
  by_cases hr : r = 0
  · subst r
    unfold avgZMod
    have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
    simp [hp]
  · simp [hr, avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hr]

lemma avgZMod_const {p : ℕ} [NeZero p] (c : ℂ) :
    avgZMod (fun _ : ZMod p => c) = c := by
  unfold avgZMod
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  simp [hp]

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ = 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = c := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, hγ, avgZMod_const]

lemma TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    (hγ : E.lift n γ ≠ 0) :
    TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  have : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [TrigPoly.finiteAverage]
  simp [TrigPoly.evalFinite_single, avgZMod_const_mul,
    avgZMod_stdAddChar_neg_mul_eq_zero_of_ne_zero hγ]

lemma TrigPoly.normalizedDftFunction_evalFinite_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (Finsupp.single γ c : E.TrigPoly) n x) r =
      if r + E.lift n γ = 0 then c else 0 := by
  rw [normalizedDftFunction_eq_avgZMod]
  simp only [TrigPoly.evalFinite_single]
  calc
    avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-(x * r)) *
            (c * ZMod.stdAddChar (-(E.lift n γ * x))))
        =
      avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          c * ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          congr 1
          funext x
          calc
            ZMod.stdAddChar (-(x * r)) *
                (c * ZMod.stdAddChar (-(E.lift n γ * x)))
                =
              c * (ZMod.stdAddChar (-(x * r)) *
                ZMod.stdAddChar (-(E.lift n γ * x))) := by
                ring
            _ =
              c * ZMod.stdAddChar (-((r + E.lift n γ) * x)) := by
                congr 1
                rw [← ZMod.stdAddChar.map_add_eq_mul]
                congr 1
                ring
    _ =
      c * avgZMod
        (fun x : ZMod (S.p (E.φ n)) =>
          ZMod.stdAddChar (-((r + E.lift n γ) * x))) := by
          rw [avgZMod_const_mul]
    _ = if r + E.lift n γ = 0 then c else 0 := by
          rw [avgZMod_stdAddChar_neg_mul_eq_ite]
          by_cases h : r + E.lift n γ = 0 <;> simp [h]

lemma TrigPoly.indicatorWeightedFiniteAverage_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) (n : ℕ) :
    TrigPoly.indicatorWeightedFiniteAverage
        (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)) := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold TrigPoly.indicatorWeightedFiniteAverage
  change avgZMod
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
    c * normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ)
  rw [show
      (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite
            (Finsupp.single γ c : E.TrigPoly) n x) =
      (fun x : ZMod (S.p (E.φ n)) =>
        c * (ZMod.stdAddChar (-(x * E.lift n γ)) *
          indicatorC (S.T (E.φ n)) x)) by
        funext x
        simp [TrigPoly.evalFinite_single]
        ring_nf]
  rw [avgZMod_const_mul]
  congr 1

lemma TrigPoly.indicatorCoeffFunctional_add
    {E : CayleyExtraction S} (P Q : E.TrigPoly) :
    TrigPoly.indicatorCoeffFunctional (P + Q) =
      TrigPoly.indicatorCoeffFunctional P +
        TrigPoly.indicatorCoeffFunctional Q := by
  unfold TrigPoly.indicatorCoeffFunctional
  let h : E.Group → ℂ →+ ℂ := fun γ =>
    { toFun := fun c => c * E.coeff γ
      map_zero' := by simp
      map_add' := by intro a b; ring }
  change Finsupp.sum (P + Q) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum Q (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

@[simp]
lemma TrigPoly.indicatorCoeffFunctional_zero
    {E : CayleyExtraction S} :
    TrigPoly.indicatorCoeffFunctional (0 : E.TrigPoly) = 0 := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.indicatorCoeffFunctional_single
    {E : CayleyExtraction S} (γ : E.Group) (c : ℂ) :
    TrigPoly.indicatorCoeffFunctional
        (Finsupp.single γ c : E.TrigPoly) =
      c * E.coeff γ := by
  simp [TrigPoly.indicatorCoeffFunctional]

lemma TrigPoly.normalizedDftFunction_evalFinite
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite P n x) r =
      P.sum fun γ c => if r + E.lift n γ = 0 then c else 0 := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [normalizedDftFunction_zero_fun]
  · intro P Q hP hQ
    have hfun :
      (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (P + Q) n x) =
        fun x =>
          TrigPoly.evalFinite P n x + TrigPoly.evalFinite Q n x := by
      funext x
      exact TrigPoly.evalFinite_add P Q n x
    rw [hfun]
    rw [normalizedDftFunction_add, hP, hQ]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change Finsupp.sum P (fun γ c => h γ c) +
        Finsupp.sum Q (fun γ c => h γ c) =
      Finsupp.sum (P + Q) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
  · intro γ c
    simpa using TrigPoly.normalizedDftFunction_evalFinite_single
      (E := E) γ c n r

lemma TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    {E : CayleyExtraction S} (P : E.TrigPoly) (n : ℕ)
    (γ : E.Group)
    (hinj :
      Set.InjOn
        (fun δ : E.Group => E.lift n δ)
        {δ : E.Group | δ ∈ insert γ P.support}) :
    P.sum (fun δ c =>
        if -E.lift n γ + E.lift n δ = 0 then c else 0) =
      P γ := by
  classical
  unfold Finsupp.sum
  rw [Finset.sum_eq_single γ]
  · simp
  · intro δ hδ hδγ
    have hnot : ¬ (-E.lift n γ + E.lift n δ = 0) := by
      intro hzero
      have heq : E.lift n δ = E.lift n γ := by
        have h := congrArg (fun z : ZMod (S.p (E.φ n)) => z + E.lift n γ) hzero
        simpa [add_comm, add_left_comm, add_assoc] using h
      exact hδγ (hinj
        (Finset.mem_insert.mpr (Or.inr hδ))
        (Finset.mem_insert_self γ P.support)
        heq)
    simp [hnot]
  · intro hγ
    have hpγ : P γ = 0 := Finsupp.notMem_support_iff.mp hγ
    simp [hpγ]

lemma TrigPoly.finiteAverage_single_zero_eventually_eq_coeff
    (E : CayleyExtraction S) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage
          (Finsupp.single (0 : E.Group) c : E.TrigPoly) n = c := by
  filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hn
  exact TrigPoly.finiteAverage_single_eq_coeff_of_lift_eq_zero
    (E := E) (0 : E.Group) c n hn

lemma finiteLift_eventually_ne_zero
    (E : CayleyExtraction S) {γ : E.Group} (hγ : γ ≠ 0) :
    ∀ᶠ n in atTop, E.lift n γ ≠ 0 :=
  E.data.finiteLift_eventually_ne_zero hγ

lemma TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero
    (E : CayleyExtraction S) {γ : E.Group}
    (hγ : γ ≠ 0) (c : ℂ) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage (Finsupp.single γ c : E.TrigPoly) n = 0 := by
  filter_upwards [E.finiteLift_eventually_ne_zero hγ] with n hn
  exact TrigPoly.finiteAverage_single_eq_zero_of_lift_ne_zero
    (E := E) γ c n hn

/-- Along relation-stable extraction data, finite averages of lifted
trigonometric polynomials are eventually their zero-frequency coefficient. -/
lemma TrigPoly.finiteAverage_eventually_eq_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      TrigPoly.finiteAverage P n = P (0 : E.Group) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.finiteAverage, avgZMod]
  · intro P Q hP hQ
    filter_upwards [hP, hQ] with n hp hq
    rw [TrigPoly.finiteAverage_add, hp, hq]
    rfl
  · intro γ c
    by_cases hγ : γ = 0
    · subst hγ
      simpa [Finsupp.single_eq_same] using
        TrigPoly.finiteAverage_single_zero_eventually_eq_coeff E c
    · filter_upwards
        [TrigPoly.finiteAverage_single_eq_zero_eventually_of_ne_zero E hγ c] with n hn
      rw [hn]
      exact (Finsupp.single_eq_of_ne (Ne.symm hγ) :
        (Finsupp.single γ c : E.TrigPoly) (0 : E.Group) = 0).symm

lemma TrigPoly.finiteAverage_tendsto_zeroCoeff
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (P (0 : E.Group))) := by
  have h :
      (fun _ : ℕ => P (0 : E.Group)) =ᶠ[atTop]
        fun n => TrigPoly.finiteAverage P n := by
    filter_upwards [TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hn
    exact hn.symm
  exact tendsto_const_nhds.congr' h

lemma TrigPoly.finiteAverage_tendsto_compactAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto (fun n => TrigPoly.finiteAverage P n) atTop
      (𝓝 (TrigPoly.compactAverage P)) := by
  simpa [TrigPoly.compactAverage] using
    TrigPoly.finiteAverage_tendsto_zeroCoeff E P

lemma TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => TrigPoly.indicatorWeightedFiniteAverage P n)
      atTop (𝓝 (TrigPoly.indicatorCoeffFunctional P)) := by
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [TrigPoly.indicatorWeightedFiniteAverage,
      TrigPoly.indicatorCoeffFunctional, avgZMod]
  · intro P Q hP hQ
    rw [TrigPoly.indicatorCoeffFunctional_add P Q]
    exact (hP.add hQ).congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_add P Q n).symm)
  · intro γ c
    rw [TrigPoly.indicatorCoeffFunctional_single γ c]
    have hcoeff := E.coeff_tendsto γ
    have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) :=
      tendsto_const_nhds
    have hmul := hc.mul hcoeff
    exact hmul.congr' (Filter.Eventually.of_forall fun n => by
      exact (TrigPoly.indicatorWeightedFiniteAverage_single γ c n).symm)

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/PairOverlap.lean
    ============================================================= -/

/-
Erdős Problem 42 — generic finite pair-overlap predicates.
-/

namespace Erdos42.CompactCayley

/-- The finite fiber of pairs in `Q × Q` with prescribed difference.  This
definition fixes the otherwise hidden decidability argument of `Finset.filter`,
so downstream bounds can share exactly the same finite set. -/
noncomputable def pairFiber {G : Type*} [Sub G] (Q : Finset G) (γ : G) :
    Finset (G × G) := by
  classical
  exact (Q.product Q).filter (fun pair => pair.1 - pair.2 = γ)

/-- Generic lower-overlap form of the Fejér coefficient bound. -/
def PairCoeffLowerBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)

/-- Absolute-error real-ratio form of the finite pair-overlap bound. -/
def PairCoeffRealBound {G : Type*} [AddGroup G]
    (Q B : Finset G) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    |1 - ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ)| ≤ M

namespace PairCoeffRealBound

variable {G : Type*} [AddGroup G]

lemma pairFilter_card_le (Q : Finset G) (γ : G) :
    (pairFiber Q γ).card ≤ Q.card := by
  classical
  let fiber := pairFiber Q γ
  have hmaps :
      Set.MapsTo (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) (↑Q : Set G) := by
    intro pair hpair
    have hpair_fin : pair ∈ fiber := by
      simpa using hpair
    have hpair' :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair_fin
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair').1).1
  have hinj :
      Set.InjOn (fun pair : G × G => pair.1) (↑fiber : Set (G × G)) := by
    intro pair hpair pair' hpair' hfirst
    have hpair_fin : pair ∈ fiber := by
      simpa using hpair
    have hpair'_fin : pair' ∈ fiber := by
      simpa using hpair'
    have hpair_mem :
        pair ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair_fin
    have hpair'_mem :
        pair' ∈ (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
      simpa only [fiber, pairFiber] using hpair'_fin
    have hdiff : pair.1 - pair.2 = γ :=
      (Finset.mem_filter.mp hpair_mem).2
    have hdiff' : pair'.1 - pair'.2 = γ :=
      (Finset.mem_filter.mp hpair'_mem).2
    have hsub : pair.1 - pair.2 = pair.1 - pair'.2 := by
      simpa [hfirst] using hdiff.trans hdiff'.symm
    have hsecond : pair.2 = pair'.2 := by
      simpa [sub_eq_sub_iff_add_eq_add] using hsub
    exact Prod.ext hfirst hsecond
  simpa [fiber] using
    Finset.card_le_card_of_injOn (fun pair : G × G => pair.1)
      hmaps hinj

lemma of_lowerBound {Q B : Finset G} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : PairCoeffLowerBound Q B M) :
    PairCoeffRealBound Q B M := by
  classical
  intro γ hγ
  have hQpos_nat : 0 < Q.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hQ)
  have hQpos : 0 < (Q.card : ℝ) := by exact_mod_cast hQpos_nat
  have hratio_le_one :
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hQpos]
    norm_num
    exact_mod_cast pairFilter_card_le Q γ
  have hratio_ge := hM γ hγ
  rw [abs_le]
  constructor <;> linarith

end PairCoeffRealBound

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Fejer.lean
    ============================================================= -/

/-
Erdős Problem 42 — Fejér kernels for compact-Cayley extraction.
-/

namespace Erdos42.CompactCayley

open Filter Complex
open scoped BigOperators ComplexConjugate Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finite cyclic lift of the Fejér kernel. -/
noncomputable def finiteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Finite cyclic lift of the compact-phase shifted Fejér kernel. -/
noncomputable def shiftedFiniteFejerKernel
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  ((Q.card : ℂ)⁻¹) *
    ((∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))) *
      star (∑ γ ∈ Q,
        E.addCharacterValue z γ *
          ZMod.stdAddChar (-(E.lift n γ * x))))

/-- Normalized finite average of the finite cyclic Fejér kernel. -/
noncomputable def finiteFejerKernelAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) => E.finiteFejerKernel Q n x

/-- One Fourier mode in the Fejér expansion. -/
noncomputable def fejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2) ((Q.card : ℂ)⁻¹)

/-- The Fejér kernel as a trigonometric polynomial. -/
noncomputable def fejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.fejerTerm Q pair

/-- One Fourier mode in the Fejér expansion, modulated by a compact-dual point.

For fixed `z`, the resulting polynomial is the Fejér kernel translated by `z`
on the compact side; on the finite side it remains a squared magnitude because
the factors `E.addCharacterValue z γ` are unit phases. -/
noncomputable def shiftedFejerTerm
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) : E.TrigPoly :=
  Finsupp.single (pair.1 - pair.2)
    ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2))

/-- The compact-phase shifted Fejér polynomial. -/
noncomputable def shiftedFejerTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.TrigPoly :=
  ∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair

lemma fejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.fejerTerm Q pair) n x =
      (Q.card : ℂ)⁻¹ *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  simp [fejerTerm, TrigPoly.evalFinite]

lemma shiftedFejerTerm_evalFinite
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (x : ZMod (S.p (E.φ n))) :
    TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x =
      ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
        ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x)) := by
  rw [shiftedFejerTerm, TrigPoly.evalFinite_single]

lemma shiftedFejerTerm_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (pair : E.Group × E.Group) (γ : E.Group) :
    (E.shiftedFejerTerm Q z pair) γ =
      (E.fejerTerm Q pair γ) * E.addCharacterValue z γ := by
  by_cases h : pair.1 - pair.2 = γ
  · subst h
    simp [shiftedFejerTerm, fejerTerm]
  · simp [shiftedFejerTerm, fejerTerm, h]

lemma shiftedFejerTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (γ : E.Group) :
    E.shiftedFejerTrigPoly Q z γ =
      (E.fejerTrigPoly Q γ) * E.addCharacterValue z γ := by
  classical
  unfold shiftedFejerTrigPoly fejerTrigPoly
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  simp_rw [E.shiftedFejerTerm_apply Q z]
  rw [Finset.sum_mul]

lemma stdAddChar_sub_fejer
    {p : ℕ} [NeZero p] (r s x : ZMod p) :
    ZMod.stdAddChar (-((r - s) * x)) =
      ZMod.stdAddChar (-(r * x)) *
        star (ZMod.stdAddChar (-(s * x))) := by
  have hstar : star (ZMod.stdAddChar (-(s * x))) =
      ZMod.stdAddChar (s * x) := by
    have h := AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := p)) (s * x)
    simp [h]
  rw [hstar]
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma sum_product_const_mul_star
    {ι : Type*} (Q : Finset ι) (a : ι → ℂ) (c : ℂ) :
    (∑ x ∈ Q.product Q, c * (a x.1 * star (a x.2))) =
      c * ((∑ x ∈ Q, a x) * star (∑ y ∈ Q, a y)) := by
  have hstar : star (∑ y ∈ Q, a y) = ∑ y ∈ Q, star (a y) := by
    simp
  rw [hstar]
  change (∑ x ∈ Q ×ˢ Q, c * (a x.1 * star (a x.2))) =
    c * ((∑ x ∈ Q, a x) * ∑ y ∈ Q, star (a y))
  rw [Finset.sum_product]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [← Finset.mul_sum]

lemma fejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.fejerTrigPoly Q) = 1 := by
  classical
  have hcard_ne : (Q.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr
      (Finset.nonempty_iff_ne_empty.mpr hQ))
  unfold TrigPoly.compactAverage fejerTrigPoly fejerTerm
  rw [Finsupp.finsetSum_apply]
  change (∑ i ∈ Q ×ˢ Q,
    (Finsupp.single (i.1 - i.2) ((Q.card : ℂ)⁻¹) :
      E.TrigPoly) (0 : E.Group)) = 1
  rw [Finset.sum_product]
  simp [Finsupp.single_apply, sub_eq_zero, hcard_ne]

lemma shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) = 1 := by
  unfold TrigPoly.compactAverage
  rw [E.shiftedFejerTrigPoly_apply Q z 0]
  have hfejer0 : (E.fejerTrigPoly Q) (0 : E.Group) = 1 := by
    simpa [TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  rw [hfejer0]
  simp

lemma fejerTrigPoly_apply_sum
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ∑ pair ∈ Q.product Q,
        if pair.1 - pair.2 = γ then (Q.card : ℂ)⁻¹ else 0 := by
  unfold fejerTrigPoly fejerTerm
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

lemma fejerTrigPoly_apply_filter_card
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) γ =
      ((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹ := by
  rw [E.fejerTrigPoly_apply_sum Q γ]
  rw [← Finset.sum_filter]
  have hfilter :
      (Q.product Q).filter (fun pair : E.Group × E.Group =>
        pair.1 - pair.2 = γ) = pairFiber Q γ := by
    ext pair
    simp [pairFiber]
  rw [hfilter]
  simp [mul_comm]

lemma pairFiber_card_neg
    (E : CayleyExtraction S)
    (Q : Finset E.Group) (γ : E.Group) :
    (pairFiber Q (-γ)).card = (pairFiber Q γ).card := by
  classical
  refine Finset.card_bij (fun pair _hpair => (pair.2, pair.1)) ?mem ?inj ?surj
  · intro pair hpair
    have hmem :
        pair ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) := by
      simpa [pairFiber] using hpair
    have hprod := (Finset.mem_filter.mp hmem).1
    have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
      Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
    have hdiff := (Finset.mem_filter.mp hmem).2
    have hdiff' : pair.2 - pair.1 = γ := by
      calc
        pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
        _ = γ := by rw [hdiff]; simp
    have hfilter' :
        (pair.2, pair.1) ∈ (Q.product Q).filter
          (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) :=
      Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
    simpa [pairFiber] using hfilter'
  · intro a ha b hb hswap
    exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
  · intro pair hpair
    refine ⟨(pair.2, pair.1), ?_, ?_⟩
    · have hmem :
          pair ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = γ) := by
        simpa [pairFiber] using hpair
      have hprod := (Finset.mem_filter.mp hmem).1
      have hprod' : (pair.2, pair.1) ∈ Q.product Q :=
        Finset.mem_product.mpr
          ⟨(Finset.mem_product.mp hprod).2, (Finset.mem_product.mp hprod).1⟩
      have hdiff := (Finset.mem_filter.mp hmem).2
      have hdiff' : pair.2 - pair.1 = -γ := by
        calc
          pair.2 - pair.1 = -(pair.1 - pair.2) := by rw [neg_sub]
          _ = -γ := by rw [hdiff]
      have hfilter' :
          (pair.2, pair.1) ∈ (Q.product Q).filter
            (fun pair : E.Group × E.Group => pair.1 - pair.2 = -γ) :=
        Finset.mem_filter.mpr ⟨hprod', hdiff'⟩
      simpa [pairFiber] using hfilter'
    · rfl

lemma fejerTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.fejerTrigPoly Q) (-γ) = (E.fejerTrigPoly Q) γ := by
  rw [E.fejerTrigPoly_apply_filter_card Q (-γ),
    E.fejerTrigPoly_apply_filter_card Q γ, E.pairFiber_card_neg Q γ]

lemma fejerTrigPoly_apply_re_eq_pairRatio
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re =
      ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).re) =
    (fiber.card : ℝ) / (Q.card : ℝ)
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [hcast]
  simp

lemma fejerTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).im = 0 := by
  let fiber := pairFiber Q γ
  rw [E.fejerTrigPoly_apply_filter_card]
  change (((fiber.card : ℂ) * (Q.card : ℂ)⁻¹).im) = 0
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [hcast]
  simp

lemma fejerTrigPoly_apply_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    0 ≤ ((E.fejerTrigPoly Q) γ).re := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  positivity

lemma fejerTrigPoly_apply_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ((E.fejerTrigPoly Q) γ).re ≤ 1 := by
  rw [E.fejerTrigPoly_apply_re_eq_pairRatio]
  exact div_le_one_of_le₀
    (by exact_mod_cast PairCoeffRealBound.pairFilter_card_le Q γ)
    (Nat.cast_nonneg Q.card)

/-- Abstract finite-frequency Fejér coefficient bound. -/
def FejerCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) γ‖ ≤ M

/-- Pair-count form of the Fejér coefficient bound. -/
def FejerPairCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B,
    ‖1 -
      (((pairFiber Q γ).card : ℂ) *
        (Q.card : ℂ)⁻¹)‖ ≤ M

/-- Real-ratio form of the pair-count Fejér coefficient bound, as produced by
Følner overlap estimates. -/
def FejerPairCoeffRealBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffRealBound Q B M

/-- Lower-overlap form of the Fejér coefficient bound.  This is the shape
normally produced by a Følner-set estimate. -/
def FejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  PairCoeffLowerBound Q B M

/-- Fejér coefficient bound on negative frequencies, the form used by the
finite DFT formula at positive extracted lifts. -/
def FejerNegCoeffBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (M : ℝ) : Prop :=
  ∀ γ ∈ B, ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M

lemma fejerCoeffBound_of_pairCoeffBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffBound Q B M) :
    E.FejerCoeffBound Q B M := by
  intro γ hγ
  rw [E.fejerTrigPoly_apply_filter_card]
  exact hM γ hγ

lemma fejerPairCoeffBound_of_realBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerPairCoeffBound Q B M := by
  intro γ hγ
  let fiber := pairFiber Q γ
  have hcast :
      ((fiber.card : ℂ) * (Q.card : ℂ)⁻¹) =
        (((fiber.card : ℝ) / (Q.card : ℝ) : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    have hfiber : (fiber.card : ℂ) = ((fiber.card : ℝ) : ℂ) := by
      norm_num
    have hQ : (Q.card : ℂ) = ((Q.card : ℝ) : ℂ) := by
      norm_num
    rw [hfiber, hQ, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  change ‖1 - (fiber.card : ℂ) * (Q.card : ℂ)⁻¹‖ ≤ M
  rw [hcast]
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  simpa [fiber, FejerPairCoeffRealBound, PairCoeffRealBound] using hM γ hγ

lemma fejerCoeffBound_of_pairCoeffRealBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerPairCoeffRealBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffBound
    (E.fejerPairCoeffBound_of_realBound hM)

lemma fejerNegCoeffBound_of_coeffBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hM : E.FejerCoeffBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M := by
  intro γ hγ
  exact hM (-γ) (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩)

lemma fejerPairCoeffRealBound_of_lowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerPairCoeffRealBound Q B M :=
  PairCoeffRealBound.of_lowerBound hQ hM

lemma fejerCoeffBound_of_pairCoeffLowerBound
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q B M) :
    E.FejerCoeffBound Q B M :=
  E.fejerCoeffBound_of_pairCoeffRealBound
    (E.fejerPairCoeffRealBound_of_lowerBound hQ hM)

lemma fejerNegCoeffBound_of_pairCoeffLowerBound_neg
    (E : CayleyExtraction S) {Q B : Finset E.Group} {M : ℝ}
    (hQ : Q ≠ ∅) (hM : E.FejerPairCoeffLowerBound Q (B.image Neg.neg) M) :
    E.FejerNegCoeffBound Q B M :=
  E.fejerNegCoeffBound_of_coeffBound_neg
    (E.fejerCoeffBound_of_pairCoeffLowerBound hQ hM)

lemma fejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x =
          E.finiteFejerKernel Q n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold fejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.fejerTerm Q pair) =
    E.finiteFejerKernel Q n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.fejerTerm Q pair) n x) =
      E.finiteFejerKernel Q n x
  simp_rw [E.fejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        (Q.card : ℂ)⁻¹ *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            (ZMod.stdAddChar (-(E.lift n pair.1 * x)) *
              star (ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [stdAddChar_sub_fejer]
    _ = E.finiteFejerKernel Q n x := by
      unfold finiteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ => ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma shiftedFejerTrigPoly_evalFinite_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        TrigPoly.evalFinite (E.shiftedFejerTrigPoly Q z) n x =
          E.shiftedFiniteFejerKernel Q z n x := by
  classical
  have hpairs :
      ∀ᶠ n in atTop,
        ∀ pair ∈ Q.product Q,
          E.lift n (pair.1 - pair.2) =
            E.lift n pair.1 - E.lift n pair.2 := by
    rw [(Q.product Q).eventually_all]
    intro pair _hpair
    exact E.data.finiteLift_sub_eventually_eq pair.1 pair.2
  filter_upwards [hpairs] with n hn x
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFejerTrigPoly
  let ev : E.TrigPoly →+ ℂ :=
    { toFun := fun P => TrigPoly.evalFinite P n x
      map_zero' := by simp
      map_add' := by
        intro P R
        exact TrigPoly.evalFinite_add P R n x }
  change ev (∑ pair ∈ Q.product Q, E.shiftedFejerTerm Q z pair) =
    E.shiftedFiniteFejerKernel Q z n x
  rw [map_sum]
  change
      (∑ pair ∈ Q.product Q,
        TrigPoly.evalFinite (E.shiftedFejerTerm Q z pair) n x) =
      E.shiftedFiniteFejerKernel Q z n x
  simp_rw [E.shiftedFejerTerm_evalFinite]
  calc
    (∑ pair ∈ Q.product Q,
        ((Q.card : ℂ)⁻¹ * E.addCharacterValue z (pair.1 - pair.2)) *
          ZMod.stdAddChar (-(E.lift n (pair.1 - pair.2) * x))) =
        ∑ pair ∈ Q.product Q,
          (Q.card : ℂ)⁻¹ *
            ((E.addCharacterValue z pair.1 *
                ZMod.stdAddChar (-(E.lift n pair.1 * x))) *
              star (E.addCharacterValue z pair.2 *
                ZMod.stdAddChar (-(E.lift n pair.2 * x)))) := by
      refine Finset.sum_congr rfl ?_
      intro pair hpair
      rw [hn pair hpair]
      rw [E.addCharacterValue_sub, stdAddChar_sub_fejer]
      rw [star_mul]
      ring
    _ = E.shiftedFiniteFejerKernel Q z n x := by
      unfold shiftedFiniteFejerKernel
      exact sum_product_const_mul_star Q
        (fun γ =>
          E.addCharacterValue z γ *
            ZMod.stdAddChar (-(E.lift n γ * x)))
        ((Q.card : ℂ)⁻¹)

lemma finiteFejerKernelAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteFejerKernelAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernelAverage TrigPoly.finiteAverage
  apply congrArg (fun f : ZMod (S.p (E.φ n)) → ℂ => avgZMod f)
  funext x
  exact (hn x).symm

lemma normalizedDftFunction_finiteFejerKernel_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ r : ZMod (S.p (E.φ n)),
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftFunction (E.finiteFejerKernel Q n) r) =
          (E.fejerTrigPoly Q).sum fun γ c =>
            if r + E.lift n γ = 0 then c else 0 := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn r
  have : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfun :
      E.finiteFejerKernel Q n =
        fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x := by
    funext x
    exact (hn x).symm
  rw [hfun]
  exact TrigPoly.normalizedDftFunction_evalFinite
    (E := E) (E.fejerTrigPoly Q) n r

lemma normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (-E.lift n γ)) =
        (E.fejerTrigPoly Q) γ := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q,
      E.data.finiteLift_eventually_injOn_finset (insert γ P.support)] with n hfourier hinj
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [hfourier (-E.lift n γ)]
  exact TrigPoly.sum_if_neg_lift_add_eq_zero_eq_apply_of_injOn
    (E := E) P n γ hinj

lemma normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)) =
        (E.fejerTrigPoly Q) (-γ) := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_neg_lift_eventually_eq_coeff
        Q (-γ),
      E.data.finiteLift_neg_eventually_eq γ] with n hcoeff hneg
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  have hfreq : -E.lift n (-γ) = E.lift n γ := by
    rw [lift, hneg]
    change - -E.data.finiteLift n γ = E.data.finiteLift n γ
    simp
  rw [← hfreq]
  exact hcoeff

lemma norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group)
    {M : ℝ} (hM : ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) (E.lift n γ)‖) ≤ M := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_at_lift_eventually_eq_coeff
      Q γ] with n hn
  rw [hn]
  exact hM

lemma finiteFejerKernelAverage_eventually_eq_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop, E.finiteFejerKernelAverage Q n = 1 := by
  let P : E.TrigPoly := E.fejerTrigPoly Q
  filter_upwards
    [E.finiteFejerKernelAverage_eventually_eq Q,
      TrigPoly.finiteAverage_eventually_eq_zeroCoeff E P] with n hkernel hpoly
  rw [hkernel, hpoly]
  exact E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ

lemma finiteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.finiteFejerKernel Q n x).re := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp only [ofReal_inv, ofReal_natCast, mul_re, inv_re, natCast_re, normSq_natCast,
    div_self_mul_self', ofReal_re, inv_im, natCast_im, neg_zero, zero_div, ofReal_im,
    mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

lemma finiteFejerKernel_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    (x : ZMod (S.p (E.φ n))) :
    (E.finiteFejerKernel Q n x).im = 0 := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteFejerKernel
  set w : ℂ := ∑ γ ∈ Q, ZMod.stdAddChar (-(E.lift n γ * x))
  change (((Q.card : ℂ)⁻¹) * (w * star w)).im = 0
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

lemma shiftedFiniteFejerKernel_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (n : ℕ) (x : ZMod (S.p (E.φ n))) :
    0 ≤ (E.shiftedFiniteFejerKernel Q z n x).re := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold shiftedFiniteFejerKernel
  set w : ℂ := ∑ γ ∈ Q,
    E.addCharacterValue z γ * ZMod.stdAddChar (-(E.lift n γ * x))
  change 0 ≤ (((Q.card : ℂ)⁻¹) * (w * star w)).re
  have hnonneg : 0 ≤ ((Q.card : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg Q.card)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  rw [show star w = conj w by rfl, Complex.mul_conj]
  simp only [ofReal_inv, ofReal_natCast, mul_re, inv_re, natCast_re, normSq_natCast,
    div_self_mul_self', ofReal_re, inv_im, natCast_im, neg_zero, zero_div, ofReal_im,
    mul_zero, sub_zero, ge_iff_le]
  exact mul_nonneg hnonneg (Complex.normSq_nonneg w)

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Smoothing.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite Fejér smoothing for compact-Cayley extraction.
-/

namespace Erdos42.CompactCayley

open Filter Complex MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Normalized convolution on `ZMod p`. -/
noncomputable def avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun x => avgZMod fun y => f (x - y) * g y

lemma stdAddChar_neg_mul_split_sub
    {p : ℕ} [NeZero p] (x y r : ZMod p) :
    ZMod.stdAddChar (-(x * r)) =
      ZMod.stdAddChar (-((x - y) * r)) *
        ZMod.stdAddChar (-(y * r)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  congr 1
  ring

lemma normalizedDftFunction_eq_avgZMod {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction f r =
      avgZMod fun x : ZMod p => ZMod.stdAddChar (-(x * r)) * f x := by
  rw [normalizedDftFunction_eq_sum]
  rfl

lemma avgZMod_comm {p : ℕ} [NeZero p] (F : ZMod p → ZMod p → ℂ) :
    avgZMod (fun x => avgZMod fun y => F x y) =
      avgZMod (fun y => avgZMod fun x => F x y) := by
  unfold avgZMod
  calc
    ((p : ℂ)⁻¹) * ∑ x : ZMod p, ((p : ℂ)⁻¹) * ∑ y : ZMod p, F x y
        = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
            ∑ x : ZMod p, ∑ y : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring
    _ = ((p : ℂ)⁻¹) * ((p : ℂ)⁻¹) *
          ∑ y : ZMod p, ∑ x : ZMod p, F x y := by
          rw [Finset.sum_comm]
    _ = ((p : ℂ)⁻¹) * ∑ y : ZMod p, ((p : ℂ)⁻¹) *
          ∑ x : ZMod p, F x y := by
          rw [← Finset.mul_sum]
          ring

lemma avgZMod_sub_right {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (y : ZMod p) :
    avgZMod (fun x => f (x - y)) = avgZMod f := by
  unfold avgZMod
  apply congrArg (fun S : ℂ => ((p : ℂ)⁻¹) * S)
  refine Fintype.sum_equiv (Equiv.addRight (-y)) _ _ ?_
  intro x
  simp [sub_eq_add_neg]

lemma avgZMod_re {p : ℕ} [NeZero p] (f : ZMod p → ℂ) :
    (avgZMod f).re = ((p : ℝ)⁻¹) * ∑ x : ZMod p, (f x).re := by
  unfold avgZMod
  rw [show ((p : ℂ)⁻¹) = (((p : ℝ)⁻¹ : ℝ) : ℂ) by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]]
  simp [Complex.mul_re]

lemma avgZMod_re_le {p : ℕ} [NeZero p] {f g : ZMod p → ℂ}
    (h : ∀ x, (f x).re ≤ (g x).re) :
    (avgZMod f).re ≤ (avgZMod g).re := by
  rw [avgZMod_re f, avgZMod_re g]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _hx => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg p))

/-- Normalized DFT sends normalized convolution to pointwise multiplication. -/
lemma normalizedDftFunction_avgConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (r : ZMod p) :
    normalizedDftFunction (avgConvolution f g) r =
      normalizedDftFunction f r * normalizedDftFunction g r := by
  classical
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgConvolution
  calc
    avgZMod
        (fun x : ZMod p =>
          ZMod.stdAddChar (-(x * r)) *
            avgZMod (fun y : ZMod p => f (x - y) * g y))
        =
      avgZMod
        (fun x : ZMod p =>
          avgZMod
            (fun y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          congr 1
          funext x
          rw [avgZMod_const_mul]
    _ =
      avgZMod
        (fun y : ZMod p =>
          avgZMod
            (fun x : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))) := by
          exact avgZMod_comm
            (fun x y : ZMod p =>
              ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
    _ =
      avgZMod
        (fun y : ZMod p =>
          normalizedDftFunction f r *
            (ZMod.stdAddChar (-(y * r)) * g y)) := by
          congr 1
          funext y
          calc
            avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-(x * r)) * (f (x - y) * g y))
                =
              avgZMod
                (fun x : ZMod p =>
                  (ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                    (ZMod.stdAddChar (-(y * r)) * g y)) := by
                congr 1
                funext x
                rw [stdAddChar_neg_mul_split_sub x y r]
                ring
            _ =
              avgZMod
                (fun x : ZMod p =>
                  ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                rw [avgZMod_mul_const]
            _ =
              normalizedDftFunction f r *
                (ZMod.stdAddChar (-(y * r)) * g y) := by
                have hshift :
                    avgZMod
                        (fun x : ZMod p =>
                          ZMod.stdAddChar (-((x - y) * r)) * f (x - y)) =
                      normalizedDftFunction f r := by
                  rw [avgZMod_sub_right
                    (fun z : ZMod p => ZMod.stdAddChar (-(z * r)) * f z) y]
                  rw [← normalizedDftFunction_eq_avgZMod]
                rw [hshift]
    _ = normalizedDftFunction f r * normalizedDftFunction g r := by
          rw [avgZMod_const_mul]
          rw [← normalizedDftFunction_eq_avgZMod]

lemma norm_normalizedDftFunction_le_norm_average
    {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (r : ZMod p) :
    ‖normalizedDftFunction f r‖ ≤
      ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
  rw [normalizedDftFunction_eq_avgZMod]
  unfold avgZMod
  calc
    ‖((p : ℂ)⁻¹) *
        ∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ x : ZMod p, ZMod.stdAddChar (-(x * r)) * f x‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ *
        ∑ x : ZMod p, ‖ZMod.stdAddChar (-(x * r)) * f x‖ := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖((p : ℂ)⁻¹)‖ * ∑ x : ZMod p, ‖f x‖ := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          rw [norm_mul, AddChar.norm_apply, one_mul]
    _ = ((p : ℝ)⁻¹) * ∑ x : ZMod p, ‖f x‖ := by
          rw [norm_inv, Complex.norm_natCast]

lemma norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_norm_avg : ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ ≤ 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 := by
  intro x
  unfold avgConvolution avgZMod
  have hsum :
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ ≤
        ∑ y : ZMod p, ‖K y‖ := by
    calc
      ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖
          ≤ ∑ y : ZMod p, ‖indicatorC T (x - y) * K y‖ := norm_sum_le _ _
      _ ≤ ∑ y : ZMod p, ‖K y‖ := by
          refine Finset.sum_le_sum ?_
          intro y _hy
          rw [norm_mul]
          have hind : ‖indicatorC T (x - y)‖ ≤ 1 := by
            classical
            by_cases h : x - y ∈ T
            · simp [indicatorC, h]
            · simp [indicatorC, h]
          exact mul_le_of_le_one_left (norm_nonneg _) hind
  calc
    ‖(↑p)⁻¹ * ∑ y : ZMod p, indicatorC T (x - y) * K y‖
        = ‖((p : ℂ)⁻¹)‖ *
            ‖∑ y : ZMod p, indicatorC T (x - y) * K y‖ := by
          rw [norm_mul]
    _ ≤ ‖((p : ℂ)⁻¹)‖ * ∑ y : ZMod p, ‖K y‖ :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ := by
          rw [norm_inv, Complex.norm_natCast]
    _ ≤ 1 := hK_norm_avg

lemma kernel_norm_average_eq_one_of_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖ = 1 := by
  have hsum_eq :
      (∑ y : ZMod p, K y) =
        ((∑ y : ZMod p, (K y).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.re_sum]
    · simp [Complex.im_sum, hK_im]
  have havg_re :
      ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re = 1 := by
    have h := congrArg Complex.re hK_avg
    unfold avgZMod at h
    rw [hsum_eq] at h
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv] at h
    simpa [Complex.ofReal_mul] using h
  calc
    ((p : ℝ)⁻¹) * ∑ y : ZMod p, ‖K y‖
        = ((p : ℝ)⁻¹) * ∑ y : ZMod p, (K y).re := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y _hy
          have hnorm := (Complex.abs_re_eq_norm).mpr (hK_im y)
          rw [← hnorm, abs_of_nonneg (hK_nonneg y)]
    _ = 1 := havg_re

lemma norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (T : Finset (ZMod p)) (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1) :
    ∀ x : ZMod p, ‖avgConvolution (indicatorC T) K x‖ ≤ 1 :=
  norm_avgConvolution_indicator_le_of_kernel_norm_average_le_one T K
    ((kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg).le)

lemma norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
    {p : ℕ} [NeZero p] (K : ZMod p → ℂ)
    (hK_nonneg : ∀ y, 0 ≤ (K y).re)
    (hK_im : ∀ y, (K y).im = 0)
    (hK_avg : avgZMod K = 1)
    (r : ZMod p) :
    ‖normalizedDftFunction K r‖ ≤ 1 :=
  (norm_normalizedDftFunction_le_norm_average K r).trans_eq
    (kernel_norm_average_eq_one_of_real_nonneg_avg_one
      K hK_nonneg hK_im hK_avg)

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- Finite Fejér-smoothed Cayley allowed kernel `1_T * K_Q`. -/
noncomputable def finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    ZMod (S.p (E.φ n)) → ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgConvolution (indicatorC (S.T (E.φ n))) (E.finiteFejerKernel Q n)

/-- Finite average of the complement indicator `1 - 1_T` weighted by a Fejér
kernel.  This is the finite inequality input for summability of `gCoeff`. -/
noncomputable def finiteComplementFejerAverage
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * E.finiteFejerKernel Q n x

/-- Finite average of the complement indicator `1 - 1_T` weighted by an
arbitrary lifted trigonometric polynomial. -/
noncomputable def finiteComplementWeightedAverage
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x

lemma finiteComplementWeightedAverage_eventually_eq
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    ∀ᶠ n in atTop,
      E.finiteComplementWeightedAverage P n =
        TrigPoly.finiteAverage P n -
          TrigPoly.indicatorWeightedFiniteAverage P n := by
  filter_upwards with n
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementWeightedAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) * TrigPoly.evalFinite P n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x -
          indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        congr 1
        funext x
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite P n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x * TrigPoly.evalFinite P n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementWeightedAverage_tendsto
    (E : CayleyExtraction S) (P : E.TrigPoly) :
    Tendsto
      (fun n => E.finiteComplementWeightedAverage P n)
      atTop
      (𝓝 (TrigPoly.compactAverage P -
        TrigPoly.indicatorCoeffFunctional P)) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E P).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E P)
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementWeightedAverage_eventually_eq P] with n hn
      exact hn.symm)

lemma finiteComplementWeightedAverage_re_nonneg
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (hP : ∀ x : ZMod (S.p (E.φ n)),
      0 ≤ (TrigPoly.evalFinite P n x).re) :
    0 ≤ (E.finiteComplementWeightedAverage P n).re := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [finiteComplementWeightedAverage, avgZMod_re]
  refine mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ?_
  refine Finset.sum_nonneg ?_
  intro x _hx
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx]
  · simpa [indicatorC, hx] using hP x

lemma shiftedFejer_complementFunctional_re_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    0 ≤
      (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re := by
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  have htendsto :=
    E.finiteComplementWeightedAverage_tendsto P
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (TrigPoly.compactAverage P - TrigPoly.indicatorCoeffFunctional P) |>.comp
      htendsto
  have hnonneg :
      ∀ᶠ n in atTop, 0 ≤ (E.finiteComplementWeightedAverage P n).re := by
    filter_upwards [E.shiftedFejerTrigPoly_evalFinite_eventually_eq Q z] with n hn
    exact E.finiteComplementWeightedAverage_re_nonneg P n (by
      intro x
      simpa [P, hn x] using E.shiftedFiniteFejerKernel_re_nonneg Q z n x)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto_re hnonneg

lemma finiteComplementFejerAverage_eventually_eq
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      E.finiteComplementFejerAverage Q n =
        TrigPoly.finiteAverage (E.fejerTrigPoly Q) n -
          TrigPoly.indicatorWeightedFiniteAverage (E.fejerTrigPoly Q) n := by
  filter_upwards [E.fejerTrigPoly_evalFinite_eventually_eq Q] with n hn
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage TrigPoly.finiteAverage
    TrigPoly.indicatorWeightedFiniteAverage
  calc
    avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        (1 - indicatorC (S.T (E.φ n)) x) *
          E.finiteFejerKernel Q n x)
        =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x -
          indicatorC (S.T (E.φ n)) x *
            TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        congr 1
        funext x
        rw [hn x]
        ring
    _ =
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) -
      avgZMod (fun x : ZMod (S.p (E.φ n)) =>
        indicatorC (S.T (E.φ n)) x *
          TrigPoly.evalFinite (E.fejerTrigPoly Q) n x) := by
        unfold avgZMod
        rw [Finset.sum_sub_distrib]
        ring

lemma finiteComplementFejerAverage_tendsto
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (TrigPoly.compactAverage (E.fejerTrigPoly Q) -
        TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  have hdiff :=
    (TrigPoly.finiteAverage_tendsto_compactAverage E
      (E.fejerTrigPoly Q)).sub
      (TrigPoly.indicatorWeightedFiniteAverage_tendsto_coeffFunctional E
        (E.fejerTrigPoly Q))
  exact hdiff.congr'
    (by
      filter_upwards [E.finiteComplementFejerAverage_eventually_eq Q] with n hn
      exact hn.symm)

lemma finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    Tendsto
      (fun n => E.finiteComplementFejerAverage Q n)
      atTop
      (𝓝 (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q))) := by
  simpa [E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ] using
    E.finiteComplementFejerAverage_tendsto Q

lemma finiteComplementFejerAverage_re_le_fejerAverage_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteComplementFejerAverage Q n).re ≤
      (E.finiteFejerKernelAverage Q n).re := by
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteComplementFejerAverage finiteFejerKernelAverage
  refine avgZMod_re_le ?_
  intro x
  by_cases hx : x ∈ S.T (E.φ n)
  · simp [indicatorC, hx, E.finiteFejerKernel_re_nonneg Q n x]
  · simp [indicatorC, hx]

lemma finiteComplementFejerAverage_re_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      (E.finiteComplementFejerAverage Q n).re ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg
  exact (E.finiteComplementFejerAverage_re_le_fejerAverage_re Q n).trans_eq
    (by simp [havg])

lemma finiteSmooth_norm_le_one_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    ∀ᶠ n in atTop,
      ∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1 := by
  filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg z
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine norm_avgConvolution_indicator_le_of_kernel_real_nonneg_avg_one
    (S.T (E.φ n)) (E.finiteFejerKernel Q n)
    (E.finiteFejerKernel_re_nonneg Q n)
    (E.finiteFejerKernel_im_eq_zero Q n) ?_ z
  simpa [finiteFejerKernelAverage] using havg

lemma normalizedDftFunction_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction (E.finiteSmooth Q n) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        normalizedDftFunction (E.finiteFejerKernel Q n) r := by
  unfold finiteSmooth
  rw [normalizedDftFunction_avgConvolution]
  rfl

/-- For a fixed finite polynomial `P`, weight its lifted finite Fourier
coefficients by the finite indicator coefficients of the extracted cyclic
model. This is the finite polynomial model for Fejér smoothing. -/
noncomputable def finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) : E.TrigPoly :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  P.sum fun γ c =>
    Finsupp.single γ
      (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)

lemma finiteDftWeightedTrigPoly_add
    (E : CayleyExtraction S) (P R : E.TrigPoly) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (P + R) n =
      E.finiteDftWeightedTrigPoly P n +
        E.finiteDftWeightedTrigPoly R n := by
  classical
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  let h : E.Group → ℂ →+ E.TrigPoly := fun γ =>
    { toFun := fun c =>
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [mul_add, Finsupp.single_add] }
  change Finsupp.sum (P + R) (fun γ c => h γ c) =
    Finsupp.sum P (fun γ c => h γ c) +
      Finsupp.sum R (fun γ c => h γ c)
  rw [Finsupp.sum_hom_add_index]

lemma finiteDftWeightedTrigPoly_single
    (E : CayleyExtraction S) (γ : E.Group) (c : ℂ) (n : ℕ) :
    E.finiteDftWeightedTrigPoly (Finsupp.single γ c : E.TrigPoly) n =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        Finsupp.single γ
          (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * c)) := by
  classical
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  unfold finiteDftWeightedTrigPoly
  rw [Finsupp.sum_single_index]
  simp

lemma finiteDftWeightedTrigPoly_apply
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ) (γ : E.Group) :
    E.finiteDftWeightedTrigPoly P n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) * P γ) := by
  classical
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    simp [hP, hR, mul_add]
  · intro δ c
    rw [E.finiteDftWeightedTrigPoly_single δ c n]
    by_cases hδγ : δ = γ
    · subst hδγ
      simp
    · have hleft :
          (Finsupp.single δ
            (normalizedDftCoeff (S.T (E.φ n)) (-E.lift n δ) * c) :
              E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      have hright : (Finsupp.single δ c : E.TrigPoly) γ = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm hδγ)
      rw [hleft, hright]
      simp

lemma normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun x : ZMod (S.p (E.φ n)) =>
          TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (P.sum fun γ c => if r + E.lift n γ = 0 then c else 0) := by
  classical
  refine Finsupp.induction_linear P ?zero ?add ?single
  · simp [finiteDftWeightedTrigPoly, normalizedDftFunction_zero_fun]
  · intro P R hP hR
    rw [E.finiteDftWeightedTrigPoly_add P R n]
    have hfun :
        (fun x : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n +
              E.finiteDftWeightedTrigPoly R n) n x) =
          fun x =>
            TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly P n) n x +
              TrigPoly.evalFinite (E.finiteDftWeightedTrigPoly R n) n x := by
      funext x
      exact TrigPoly.evalFinite_add
        (E.finiteDftWeightedTrigPoly P n)
        (E.finiteDftWeightedTrigPoly R n) n x
    rw [hfun, normalizedDftFunction_add, hP, hR]
    let h : E.Group → ℂ →+ ℂ := fun γ =>
      { toFun := fun c => if r + E.lift n γ = 0 then c else 0
        map_zero' := by by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ]
        map_add' := by
          intro a b
          by_cases hγ : r + E.lift n γ = 0 <;> simp [hγ] }
    change normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum P (fun γ c => h γ c) +
        normalizedDftCoeff (S.T (E.φ n)) r *
          Finsupp.sum R (fun γ c => h γ c) =
      normalizedDftCoeff (S.T (E.φ n)) r *
        Finsupp.sum (P + R) (fun γ c => h γ c)
    rw [Finsupp.sum_hom_add_index]
    ring
  · intro γ c
    rw [E.finiteDftWeightedTrigPoly_single γ c n]
    rw [TrigPoly.normalizedDftFunction_evalFinite_single]
    by_cases hγ : r + E.lift n γ = 0
    · have hr : r = -E.lift n γ := eq_neg_of_add_eq_zero_left hγ
      simp [hr]
    · simp [hγ]

/-- The finite trigonometric polynomial whose lifted evaluation is eventually
the fixed-`Q` finite Fejér-smoothed kernel. -/
noncomputable def finiteSmoothModelTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) : E.TrigPoly :=
  E.finiteDftWeightedTrigPoly (E.fejerTrigPoly Q) n

lemma finiteSmoothModelTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) (γ : E.Group) :
    E.finiteSmoothModelTrigPoly Q n γ =
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ) *
          (E.fejerTrigPoly Q) γ) := by
  simp [finiteSmoothModelTrigPoly, E.finiteDftWeightedTrigPoly_apply]

lemma finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    ∀ᶠ n in atTop,
      ∀ x : ZMod (S.p (E.φ n)),
        E.finiteSmooth Q n x =
          TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x := by
  filter_upwards
    [E.normalizedDftFunction_finiteFejerKernel_eventually_eq Q] with n hK x
  have : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (E.finiteSmooth Q n) x]
  rw [function_eq_sum_normalizedDftFunction (p := S.p (E.φ n))
      (fun x : ZMod (S.p (E.φ n)) =>
        TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n x) x]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  congr 1
  rw [E.normalizedDftFunction_finiteSmooth Q n r, hK r]
  rw [finiteSmoothModelTrigPoly,
    E.normalizedDftFunction_evalFinite_finiteDftWeightedTrigPoly
      (E.fejerTrigPoly Q) n r]

lemma normalizedDftFunction_indicator_sub_finiteSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ)
    [NeZero (S.p (E.φ n))]
    (r : ZMod (S.p (E.φ n))) :
    normalizedDftFunction
        (fun z : ZMod (S.p (E.φ n)) =>
          indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z) r =
      normalizedDftCoeff (S.T (E.φ n)) r *
        (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r) := by
  rw [normalizedDftFunction_sub, E.normalizedDftFunction_finiteSmooth Q n r]
  simp [normalizedDftCoeff]
  ring

/-- Compact-side trigonometric polynomial whose coefficients match the
fixed-`Q` Fejér-smoothed Cayley limit. -/
noncomputable def compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) : E.TrigPoly :=
  ∑ γ ∈ (E.fejerTrigPoly Q).support,
    Finsupp.single γ ((E.fejerTrigPoly Q) γ * E.coeff (-γ))

lemma compactSmoothTrigPoly_apply
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q γ =
      (E.fejerTrigPoly Q) γ * E.coeff (-γ) := by
  classical
  unfold compactSmoothTrigPoly
  rw [Finsupp.finsetSum_apply]
  by_cases hγ : γ ∈ (E.fejerTrigPoly Q).support
  · rw [Finset.sum_eq_single γ]
    · simp
    · intro δ hδ hδγ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)
    · intro hnot
      exact (hnot hγ).elim
  · have hzero : (E.fejerTrigPoly Q) γ = 0 :=
      Finsupp.notMem_support_iff.mp hγ
    rw [Finset.sum_eq_zero]
    · rw [hzero]
      simp
    · intro δ hδ
      have hδγ : δ ≠ γ := by
        intro h
        subst h
        exact hγ hδ
      exact Finsupp.single_eq_of_ne (Ne.symm hδγ)

lemma finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    Tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n γ)
      atTop (𝓝 (E.compactSmoothTrigPoly Q γ)) := by
  have hcoeff := E.coeff_tendsto (-γ)
  have hcoeff' :
      Tendsto
        (fun n =>
          letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (-E.lift n γ))
        atTop (𝓝 (E.coeff (-γ))) := by
    refine hcoeff.congr' ?_
    filter_upwards [E.data.finiteLift_neg_eventually_eq γ] with n hneg
    have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    simp [lift, hneg]
    rfl
  have hconst :
      Tendsto (fun _n : ℕ => (E.fejerTrigPoly Q) γ)
        atTop (𝓝 ((E.fejerTrigPoly Q) γ)) :=
    tendsto_const_nhds
  have hprod := hcoeff'.mul hconst
  have htarget :
      E.coeff (-γ) * (E.fejerTrigPoly Q γ) =
        E.compactSmoothTrigPoly Q γ := by
    rw [E.compactSmoothTrigPoly_apply Q γ]
    ring
  have hprod' := hprod.congr' (by
    filter_upwards with n
    exact (E.finiteSmoothModelTrigPoly_apply Q n γ).symm)
  simpa [htarget] using hprod'

/-- Compact finite-Fejér smoothing of the limiting allowed kernel, represented
by the fixed trigonometric polynomial whose coefficients are the limits of the
finite smoothed kernels. -/
noncomputable def compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℂ :=
  fun z => TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z

noncomputable def compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.CompactAddDual → ℝ :=
  fun z => (E.compactSmooth Q z).re

lemma TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (hneg : ∀ γ : E.Group, P (-γ) = P γ)
    (him : ∀ γ : E.Group, (P γ).im = 0)
    (z : E.CompactAddDual) :
    (TrigPoly.evalAdd P z).im = 0 := by
  classical
  have hsupport_neg : ∀ {γ : E.Group}, γ ∈ P.support → -γ ∈ P.support := by
    intro γ hγ
    rw [Finsupp.mem_support_iff] at hγ ⊢
    intro hzero
    have hPγ : P γ = 0 := by
      rw [← hneg γ, hzero]
    exact hγ hPγ
  have hsum :
      TrigPoly.evalAdd P z =
        ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := P) (s := P.support) (by intro γ hγ; exact hγ)]
    intro γ _hγ
    simp
  have hstar : star (TrigPoly.evalAdd P z) = TrigPoly.evalAdd P z := by
    calc
      star (TrigPoly.evalAdd P z)
          = ∑ γ ∈ P.support, star (P γ * E.addCharacterValue z γ) := by
            rw [hsum]
            simp
      _ = ∑ γ ∈ P.support, P (-γ) * E.addCharacterValue z (-γ) := by
            refine Finset.sum_congr rfl ?_
            intro γ _hγ
            have hreal : star (P γ) = P γ := by
              simpa using (Complex.conj_eq_iff_im.mpr (him γ))
            rw [star_mul, E.star_addCharacterValue, hreal, ← hneg γ]
            ring
      _ = ∑ γ ∈ P.support, P γ * E.addCharacterValue z γ := by
            refine Finset.sum_bij (fun γ _hγ => -γ) ?mem ?inj ?surj ?eq
            · intro γ hγ
              exact hsupport_neg hγ
            · intro a _ha b _hb h
              exact neg_inj.mp h
            · intro b hb
              refine ⟨-b, hsupport_neg hb, ?_⟩
              simp
            · intro γ hγ
              simp
      _ = TrigPoly.evalAdd P z := hsum.symm
  exact Complex.conj_eq_iff_im.mp hstar

lemma compactSmoothTrigPoly_apply_neg
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    E.compactSmoothTrigPoly Q (-γ) = E.compactSmoothTrigPoly Q γ := by
  rw [E.compactSmoothTrigPoly_apply Q (-γ),
    E.compactSmoothTrigPoly_apply Q γ,
    E.fejerTrigPoly_apply_neg Q γ]
  simp [E.coeff_neg_eq γ]

lemma compactSmoothTrigPoly_apply_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (γ : E.Group) :
    (E.compactSmoothTrigPoly Q γ).im = 0 := by
  rw [E.compactSmoothTrigPoly_apply Q γ]
  have hK : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hcoeff : (E.coeff (-γ)).im = 0 := E.coeff_im_eq_zero (-γ)
  simp [Complex.mul_im, hK, hcoeff]

lemma compactSmooth_im_eq_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    (E.compactSmooth Q z).im = 0 := by
  exact TrigPoly.evalAdd_im_eq_zero_of_apply_neg_eq_self E
    (E.compactSmoothTrigPoly Q)
    (E.compactSmoothTrigPoly_apply_neg Q)
    (E.compactSmoothTrigPoly_apply_im_eq_zero Q) z

lemma compactSmooth_eq_ofReal_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual) :
    E.compactSmooth Q z = (E.compactSmoothReal Q z : ℂ) := by
  apply Complex.ext
  · simp [compactSmoothReal]
  · simp [compactSmoothReal, E.compactSmooth_im_eq_zero Q z]

lemma compactSmooth_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmooth Q) :=
  TrigPoly.continuous_evalAdd E (E.compactSmoothTrigPoly Q)

lemma compactSmoothReal_continuous
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    Continuous (E.compactSmoothReal Q) :=
  Complex.continuous_re.comp (E.compactSmooth_continuous Q)

lemma compactSmoothReal_eq_sum_of_support_subset
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (A : Finset E.Group) (hA : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      ∑ γ ∈ A,
        ((E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
          (E.addCharacterValue z γ).re) := by
  classical
  have hsum :
      TrigPoly.evalAdd (E.compactSmoothTrigPoly Q) z =
        ∑ γ ∈ A,
          E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ := by
    unfold TrigPoly.evalAdd
    rw [Finsupp.sum_of_support_subset
      (f := E.compactSmoothTrigPoly Q) (s := A) hA]
    intro γ _hγ
    simp
  unfold compactSmoothReal compactSmooth
  rw [hsum]
  change Complex.reAddGroupHom
      (∑ γ ∈ A,
        E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro γ hγ
  change (E.compactSmoothTrigPoly Q γ * E.addCharacterValue z γ).re =
    (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  rw [E.compactSmoothTrigPoly_apply Q γ, E.coeff_neg_eq γ]
  have hKim : ((E.fejerTrigPoly Q) γ).im = 0 :=
    E.fejerTrigPoly_apply_im_eq_zero Q γ
  have hAim : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
  simp [Complex.mul_re, Complex.mul_im, hKim, hAim, mul_assoc]

/-- Finite average pairing the smoothed Cayley kernel with a lifted fixed
trigonometric polynomial. -/
noncomputable def finiteSmoothWeightedAverage
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) (n : ℕ) : ℂ :=
  letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  avgZMod fun x : ZMod (S.p (E.φ n)) =>
    E.finiteSmooth Q n x * P.evalFinite n x

/-- Coefficient functional that is the fixed-`Q` limit of
`finiteSmoothWeightedAverage`. -/
noncomputable def smoothedCoeffFunctional
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (P : E.TrigPoly) : ℂ :=
  P.sum fun γ c => c * (E.coeff γ * (E.fejerTrigPoly Q) (-γ))

@[simp]
lemma smoothedCoeffFunctional_zero
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    E.smoothedCoeffFunctional Q (0 : E.TrigPoly) = 0 := by
  simp [smoothedCoeffFunctional]

/-- Fejér smoothing is spectrally close to the original indicator once the
chosen Fejér polynomial is close to `1` on the extracted large-spectrum
generators.  The small-spectrum branch gives the explicit `2 / q` term. -/
lemma spectralBound_indicator_sub_finiteSmooth_eventually
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : ∀ γ ∈ E.data.largeSpectrumGenerators q,
      ‖1 - (E.fejerTrigPoly Q) (-γ)‖ ≤ M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) := by
  classical
  have hcovered := E.eventually_largeSpectrum_covered q
  have hfejerLarge :
      ∀ᶠ n in atTop,
        ∀ γ ∈ E.data.largeSpectrumGenerators q,
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n)
              (E.lift n γ)‖) ≤ M := by
    rw [(E.data.largeSpectrumGenerators q).eventually_all]
    intro γ hγ
    exact E.norm_one_sub_normalizedDftFunction_finiteFejerKernel_at_lift_eventually_le
      Q γ (hM γ hγ)
  have hfejerNorm :
      ∀ᶠ n in atTop,
        ∀ r : ZMod (S.p (E.φ n)),
          (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
            ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖) ≤ 1 := by
    filter_upwards [E.finiteFejerKernelAverage_eventually_eq_one Q hQ] with n havg r
    have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    refine norm_normalizedDftFunction_le_one_of_kernel_real_nonneg_avg_one
      (E.finiteFejerKernel Q n)
      (E.finiteFejerKernel_re_nonneg Q n)
      (E.finiteFejerKernel_im_eq_zero Q n) ?_ r
    simpa [finiteFejerKernelAverage] using havg
  filter_upwards [hcovered, hfejerLarge, hfejerNorm] with n hncover hnlarge hnnorm
  intro r
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  rw [E.normalizedDftFunction_indicator_sub_finiteSmooth Q n r]
  by_cases hsmall :
      ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ ((q : ℝ)⁻¹ : ℝ)
  · have h1K :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤
          (2 : ℝ) := by
      calc
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖
            ≤ ‖(1 : ℂ)‖ +
                ‖normalizedDftFunction (E.finiteFejerKernel Q n) r‖ :=
              norm_sub_le _ _
        _ ≤ 1 + 1 := by
              exact add_le_add (by norm_num) (hnnorm r)
        _ = (2 : ℝ) := by norm_num
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ ((q : ℝ)⁻¹ : ℝ) * 2 := by
          exact mul_le_mul hsmall h1K (norm_nonneg _) (by positivity)
      _ = 2 * ((q : ℝ)⁻¹ : ℝ) := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_left _ _
  · have hlarge :
        ((q : ℝ)⁻¹ : ℝ) <
          ‖normalizedDftCoeff (S.T (E.φ n)) r‖ := lt_of_not_ge hsmall
    rcases hncover r (by simpa using hlarge) with ⟨γ, hγ, hγr⟩
    have hK :
        ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ ≤ M := by
      simpa [hγr] using hnlarge γ hγ
    have hcoef_le :
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ ≤ 1 := by
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) r
    calc
      ‖normalizedDftCoeff (S.T (E.φ n)) r *
          (1 - normalizedDftFunction (E.finiteFejerKernel Q n) r)‖
          =
        ‖normalizedDftCoeff (S.T (E.φ n)) r‖ *
          ‖1 - normalizedDftFunction (E.finiteFejerKernel Q n) r‖ := by
          rw [norm_mul]
      _ ≤ 1 * M := by
          exact mul_le_mul hcoef_le hK (norm_nonneg _) (by norm_num)
      _ = M := by ring
      _ ≤ max (2 * ((q : ℝ)⁻¹ : ℝ)) M := le_max_right _ _

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM : E.FejerNegCoeffBound Q (E.data.largeSpectrumGenerators q) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually q Q hQ hM

lemma spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
    (E : CayleyExtraction S) (q : ℕ+) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ}
    (hM :
      E.FejerPairCoeffLowerBound Q
        ((E.data.largeSpectrumGenerators q).image Neg.neg) M) :
    ∀ᶠ n in atTop,
      (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
        SpectralBound
          (fun z : ZMod (S.p (E.φ n)) =>
            indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
          (max (2 * ((q : ℝ)⁻¹ : ℝ)) M)) :=
  E.spectralBound_indicator_sub_finiteSmooth_eventually_of_negCoeffBound q Q hQ
    (E.fejerNegCoeffBound_of_pairCoeffLowerBound_neg hQ hM)

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Folner.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite Følner overlap infrastructure.

This file isolates the finite pair-count lower bound from the extraction
structure.  The later constructive box estimate can then be proved in a
standard free abelian model and transported back to finite generated
subgroups of the extraction group.
-/

namespace Erdos42.CompactCayley

open scoped BigOperators

noncomputable section

namespace PairCoeffLowerBound

variable {G H : Type*} [AddGroup G] [AddGroup H]

def addEquivEmbedding (e : G ≃+ H) : G ↪ H :=
  e.toEquiv.toEmbedding

def addMonoidHomEmbedding (f : G →+ H) (hf : Function.Injective f) : G ↪ H where
  toFun := f
  inj' := hf

lemma pairFiber_card_map_addEquiv
    (e : G ≃+ H) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addEquivEmbedding e))
        ((addEquivEmbedding e) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addEquivEmbedding e)) ((addEquivEmbedding e) γ) =
        ((Q.map (addEquivEmbedding e)).product
          (Q.map (addEquivEmbedding e))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addEquivEmbedding e) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (e pair.1, e pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : e (pair.1 - pair.2) = e γ := congrArg e hpair.2
      simpa [addEquivEmbedding, e.map_sub] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (e.injective (congrArg Prod.fst h))
      (e.injective (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff :
            (addEquivEmbedding e) (a - b) = (addEquivEmbedding e) γ := by
          have htarget :
              (addEquivEmbedding e) a - (addEquivEmbedding e) b =
                (addEquivEmbedding e) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addEquivEmbedding, e.map_sub] using htarget
        exact e.injective (by simpa [addEquivEmbedding] using hdiff)
    · exact Prod.ext ha hb

lemma pairFiber_card_map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) (Q : Finset G) (γ : G) :
    (pairFiber (Q.map (addMonoidHomEmbedding f hf))
        ((addMonoidHomEmbedding f hf) γ)).card =
      (pairFiber Q γ).card := by
  classical
  have hleft :
      pairFiber (Q.map (addMonoidHomEmbedding f hf))
          ((addMonoidHomEmbedding f hf) γ) =
        ((Q.map (addMonoidHomEmbedding f hf)).product
          (Q.map (addMonoidHomEmbedding f hf))).filter
          (fun pair : H × H => pair.1 - pair.2 =
            (addMonoidHomEmbedding f hf) γ) := by
    ext pair
    simp [pairFiber]
  have hright :
      pairFiber Q γ =
        (Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ) := by
    ext pair
    simp [pairFiber]
  rw [hleft, hright]
  symm
  apply Finset.card_bij (fun pair _hpair => (f pair.1, f pair.2))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    rw [Finset.mem_filter]
    constructor
    · apply Finset.mem_product.mpr
      have hprod := Finset.mem_product.mp hpair.1
      exact
        ⟨Finset.mem_map.mpr ⟨pair.1, hprod.1, rfl⟩,
          Finset.mem_map.mpr ⟨pair.2, hprod.2, rfl⟩⟩
    · have hdiff : f (pair.1 - pair.2) = f γ := congrArg f hpair.2
      simpa [addMonoidHomEmbedding] using hdiff
  · intro pair _hpair pair' _hpair' h
    exact Prod.ext
      (hf (congrArg Prod.fst h))
      (hf (congrArg Prod.snd h))
  · intro pair hpair
    rw [Finset.mem_filter] at hpair
    have hprod := Finset.mem_product.mp hpair.1
    rcases Finset.mem_map.mp hprod.1 with ⟨a, haQ, ha⟩
    rcases Finset.mem_map.mp hprod.2 with ⟨b, hbQ, hb⟩
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨haQ, hbQ⟩
      · have hdiff : f (a - b) = f γ := by
          have htarget :
              (addMonoidHomEmbedding f hf) a - (addMonoidHomEmbedding f hf) b =
                (addMonoidHomEmbedding f hf) γ := by
            rw [ha, hb]
            exact hpair.2
          simpa [addMonoidHomEmbedding] using htarget
        exact hf hdiff
    · exact Prod.ext ha hb

lemma map_addEquiv
    (e : G ≃+ H) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addEquivEmbedding e)) (B.map (addEquivEmbedding e)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addEquiv, Finset.card_map]
  exact h δ hδ

lemma map_addMonoidHom_of_injective
    (f : G →+ H) (hf : Function.Injective f) {Q B : Finset G} {M : ℝ}
    (h : PairCoeffLowerBound Q B M) :
    PairCoeffLowerBound
      (Q.map (addMonoidHomEmbedding f hf)) (B.map (addMonoidHomEmbedding f hf)) M := by
  classical
  intro γ hγ
  rcases Finset.mem_map.mp hγ with ⟨δ, hδ, rfl⟩
  rw [pairFiber_card_map_addMonoidHom_of_injective, Finset.card_map]
  exact h δ hδ

lemma exists_of_addEquiv
    (e : G ≃+ H) {B : Finset G} {M : ℝ}
    (h :
      ∃ Q : Finset H, Q.Nonempty ∧
        PairCoeffLowerBound Q (B.map (addEquivEmbedding e)) M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  rcases h with ⟨Q, hQ, hbound⟩
  refine ⟨Q.map (addEquivEmbedding e.symm), ?_, ?_⟩
  · rcases hQ with ⟨q, hq⟩
    exact ⟨e.symm q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  have hmap := map_addEquiv e.symm hbound
  simpa [addEquivEmbedding, Finset.map_map] using hmap

end PairCoeffLowerBound

section PairFiberCounting

variable {G : Type*} [AddCommGroup G]

/-- Any set whose `γ`-backward translate stays inside `Q` injects into the
pair fiber `{(x,y) ∈ Q × Q | x - y = γ}`. -/
lemma card_le_pairFiber_card_of_sub_right_subset
    (Q R : Finset G) (γ : G)
    (hR : ∀ x ∈ R, x ∈ Q ∧ x - γ ∈ Q) :
    R.card ≤
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun x : G => (x, x - γ)) ?_ ?_
  · intro x hx
    change (x, x - γ) ∈
      ((Q.product Q).filter (fun pair : G × G => pair.1 - pair.2 = γ))
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr ⟨(hR x hx).1, (hR x hx).2⟩
    · simp [sub_eq_add_neg, add_left_comm]
  · intro x _hx y _hy hxy
    exact congrArg Prod.fst hxy

lemma pairCoeffLowerBound_of_inner_card
    {Q B : Finset G} {M : ℝ}
    (inner : G → Finset G)
    (hinner : ∀ γ ∈ B, ∀ x ∈ inner γ, x ∈ Q ∧ x - γ ∈ Q)
    (hcard :
      ∀ γ ∈ B,
        1 - M ≤ ((inner γ).card : ℝ) / (Q.card : ℝ)) :
    PairCoeffLowerBound Q B M := by
  classical
  intro γ hγ
  have hle :
      ((inner γ).card : ℝ) ≤
        (((Q.product Q).filter
          (fun pair : G × G => pair.1 - pair.2 = γ)).card : ℝ) := by
    exact_mod_cast
      card_le_pairFiber_card_of_sub_right_subset Q (inner γ) γ
        (hinner γ hγ)
  exact (hcard γ hγ).trans (div_le_div_of_nonneg_right hle (by positivity))

end PairFiberCounting

section IntIntervals

/-- Centered integer interval `[-N,N]`. -/
def intCenteredInterval (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- Inner interval that stays inside `[-N,N]` after subtracting any integer of
absolute value at most `K`. -/
def intInnerInterval (N K : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ) + (K : ℤ)) ((N : ℤ) - (K : ℤ))

lemma intCenteredInterval_nonempty (N : ℕ) :
    (intCenteredInterval N).Nonempty := by
  refine ⟨0, ?_⟩
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor
  · exact neg_nonpos.mpr (by exact_mod_cast Nat.zero_le N)
  · exact_mod_cast Nat.zero_le N

lemma intCenteredInterval_card (N : ℕ) :
    (intCenteredInterval N).card = 2 * N + 1 := by
  rw [intCenteredInterval, Int.card_Icc]
  omega

lemma intInnerInterval_card {N K : ℕ} (hK : K ≤ N) :
    (intInnerInterval N K).card = 2 * (N - K) + 1 := by
  rw [intInnerInterval, Int.card_Icc]
  omega

lemma intInnerInterval_subset_centered
    {N K : ℕ} :
    intInnerInterval N K ⊆ intCenteredInterval N := by
  intro x hx
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  constructor <;> nlinarith

lemma intInnerInterval_sub_mem_centered
    {N K : ℕ} {γ x : ℤ}
    (hγ : γ.natAbs ≤ K) (hx : x ∈ intInnerInterval N K) :
    x - γ ∈ intCenteredInterval N := by
  rw [intInnerInterval, Finset.mem_Icc] at hx
  rw [intCenteredInterval, Finset.mem_Icc]
  have hγ_le_K : γ ≤ (K : ℤ) := by
    exact le_trans Int.le_natAbs (by exact_mod_cast hγ)
  have hnegK_le_γ : -(K : ℤ) ≤ γ := by
    have hneg_abs : -((γ.natAbs : ℤ)) ≤ γ := by
      exact neg_le.mp (by simpa using (Int.le_natAbs (a := -γ)))
    have hγZ : (γ.natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast hγ
    exact le_trans (neg_le_neg hγZ) hneg_abs
  constructor <;> nlinarith [hx.1, hx.2, hγ_le_K, hnegK_le_γ]

end IntIntervals

section IntPiBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product box `[-N,N]^ι` in the finite-rank free abelian group `ι → Z`. -/
def intPiCenteredBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intCenteredInterval N

/-- Inner product box that stays inside `[-N,N]^ι` after subtracting any vector
whose coordinates have absolute value at most `K`. -/
def intPiInnerBox (ι : Type*) [Fintype ι] [DecidableEq ι]
    (N K : ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => intInnerInterval N K

lemma intPiCenteredBox_nonempty (N : ℕ) :
    (intPiCenteredBox ι N).Nonempty := by
  rw [intPiCenteredBox, Fintype.piFinset_nonempty]
  intro i
  exact intCenteredInterval_nonempty N

lemma intPiCenteredBox_card (N : ℕ) :
    (intPiCenteredBox ι N).card = ∏ _i : ι, (2 * N + 1 : ℕ) := by
  rw [intPiCenteredBox, Fintype.card_piFinset]
  simp [intCenteredInterval_card]

lemma intPiInnerBox_card {N K : ℕ} (hK : K ≤ N) :
    (intPiInnerBox ι N K).card =
      ∏ _i : ι, (2 * (N - K) + 1 : ℕ) := by
  rw [intPiInnerBox, Fintype.card_piFinset]
  simp [intInnerInterval_card hK]

lemma intPiInnerBox_subset_centered
    {N K : ℕ} {x : ι → ℤ}
    (hx : x ∈ intPiInnerBox ι N K) :
    x ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  exact intInnerInterval_subset_centered (hx i)

lemma intPiInnerBox_sub_mem_centered
    {N K : ℕ} {γ x : ι → ℤ}
    (hγ : ∀ i : ι, (γ i).natAbs ≤ K)
    (hx : x ∈ intPiInnerBox ι N K) :
    x - γ ∈ intPiCenteredBox ι N := by
  rw [intPiInnerBox, Fintype.mem_piFinset] at hx
  rw [intPiCenteredBox, Fintype.mem_piFinset]
  intro i
  simpa using intInnerInterval_sub_mem_centered (hγ i) (hx i)

lemma intPi_pairCoeffLowerBound_of_inner_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((intPiInnerBox ι N K).card : ℝ) /
          ((intPiCenteredBox ι N).card : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M := by
  classical
  refine pairCoeffLowerBound_of_inner_card
    (Q := intPiCenteredBox ι N) (B := B) (M := M)
    (fun _γ => intPiInnerBox ι N K) ?_ ?_
  · intro γ hγ x hx
    exact
      ⟨intPiInnerBox_subset_centered hx,
        intPiInnerBox_sub_mem_centered (hB γ hγ) hx⟩
  · intro γ _hγ
    exact hratio

lemma intPi_pairCoeffLowerBound_of_nat_ratio
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hratio :
      1 - M ≤
        ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_inner_ratio hB (by
    simpa [intPiInnerBox_card (ι := ι) hK, intPiCenteredBox_card (ι := ι)]
      using hratio)

omit [DecidableEq ι] in
lemma intPi_product_ratio_bound
    {N K : ℕ} {M : ℝ} (hK : K ≤ N)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    1 - M ≤
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
        ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := by
  classical
  let d : ℕ := Fintype.card ι
  let inner : ℝ := ((2 * (N - K) + 1 : ℕ) : ℝ)
  let outer : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have houter_pos : 0 < outer := by
    dsimp [outer]
    positivity
  have hinner_nonneg : 0 ≤ inner := by
    dsimp [inner]
    positivity
  have hratio_eq :
      ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) =
        (inner / outer) ^ d := by
    simp [d, inner, outer, Finset.prod_const, Finset.card_univ, div_pow]
  have hratio_nonneg : 0 ≤ inner / outer :=
    div_nonneg hinner_nonneg houter_pos.le
  have hbernoulli :
      1 + (d : ℝ) * (inner / outer - 1) ≤ (inner / outer) ^ d :=
    one_add_mul_sub_le_pow (a := inner / outer) (n := d) (by linarith)
  have hinner_eq : inner = outer - (2 * K : ℝ) := by
    dsimp [inner, outer]
    norm_num [Nat.cast_sub hK]
    ring
  have hsub :
      inner / outer - 1 = -((2 * K : ℝ) / outer) := by
    rw [hinner_eq]
    field_simp [houter_pos.ne']
    ring
  have hdiv_loss' :
      (((d : ℝ) * (2 * K : ℝ)) / outer) ≤ M := by
    rw [div_le_iff₀ houter_pos]
    simpa [d, outer] using hloss
  have hdiv_loss :
      (d : ℝ) * ((2 * K : ℝ) / outer) ≤ M := by
    simpa [mul_div_assoc] using hdiv_loss'
  have hlower :
      1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := by
    rw [hsub]
    nlinarith
  calc
    1 - M ≤ 1 + (d : ℝ) * (inner / outer - 1) := hlower
    _ ≤ (inner / outer) ^ d := hbernoulli
    _ = ((∏ _i : ι, (2 * (N - K) + 1 : ℕ)) : ℝ) /
          ((∏ _i : ι, (2 * N + 1 : ℕ)) : ℝ) := hratio_eq.symm

lemma intPi_pairCoeffLowerBound_of_loss
    {B : Finset (ι → ℤ)} {N K : ℕ} {M : ℝ}
    (hK : K ≤ N)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K)
    (hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ)) :
    PairCoeffLowerBound (intPiCenteredBox ι N) B M :=
  intPi_pairCoeffLowerBound_of_nat_ratio hK hB
    (intPi_product_ratio_bound (ι := ι) hK hloss)

omit [Fintype ι] [DecidableEq ι] in
lemma exists_intPi_pairCoeffLowerBound_of_bound
    [Finite ι]
    (B : Finset (ι → ℤ)) (K : ℕ) {M : ℝ} (hM : 0 < M)
    (hB : ∀ γ ∈ B, ∀ i : ι, (γ i).natAbs ≤ K) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨N, hN⟩ :=
    exists_nat_gt ((((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) + (K : ℝ))
  have hN_gt_K : (K : ℝ) < (N : ℝ) := by
    have hterm_nonneg :
        0 ≤ (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) := by
      positivity
    nlinarith [hN]
  have hKle : K ≤ N := by exact_mod_cast le_of_lt hN_gt_K
  have hloss :
      ((Fintype.card ι : ℝ) * (2 * K : ℝ)) ≤
        M * ((2 * N + 1 : ℕ) : ℝ) := by
    have hNbig :
        (((Fintype.card ι : ℝ) * (2 * K : ℝ)) / M) < (N : ℝ) := by
      nlinarith [hN]
    have hlt :
        ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < M * (N : ℝ) := by
      have hraw :
          ((Fintype.card ι : ℝ) * (2 * K : ℝ)) < (N : ℝ) * M := by
        rwa [div_lt_iff₀ hM] at hNbig
      nlinarith
    have hN_le : (N : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : N ≤ 2 * N + 1)
    exact (le_of_lt hlt).trans
      (mul_le_mul_of_nonneg_left hN_le (le_of_lt hM))
  exact
    ⟨intPiCenteredBox ι N, intPiCenteredBox_nonempty N,
      intPi_pairCoeffLowerBound_of_loss hKle hB hloss⟩

omit [Fintype ι] [DecidableEq ι] in
lemma exists_intPi_pairCoeffLowerBound
    [Finite ι]
    (B : Finset (ι → ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι → ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let := Fintype.ofFinite ι
  let C : Finset ℕ :=
    B.biUnion fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs
  by_cases hC : C.Nonempty
  · let K : ℕ := C.max' hC
    exact exists_intPi_pairCoeffLowerBound_of_bound B K hM (by
      intro γ hγ i
      exact C.le_max' (γ i).natAbs (by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩))
  · exact exists_intPi_pairCoeffLowerBound_of_bound B 0 hM (by
      intro γ hγ i
      exfalso
      exact hC ⟨(γ i).natAbs, by
        change (γ i).natAbs ∈
          B.biUnion (fun γ => (Finset.univ : Finset ι).image fun i => (γ i).natAbs)
        rw [Finset.mem_biUnion]
        exact ⟨γ, hγ, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩⟩)

end IntPiBoxes

section FinsuppBoxes

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma exists_finsupp_pairCoeffLowerBound
    [Finite ι]
    (B : Finset (ι →₀ ℤ)) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset (ι →₀ ℤ), Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let := Fintype.ofFinite ι
  let e : (ι →₀ ℤ) ≃+ (ι → ℤ) :=
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_intPi_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

end FinsuppBoxes

section FreeFinite

variable {G : Type*} [AddCommGroup G]

lemma exists_free_finite_pairCoeffLowerBound
    [Module.Free ℤ G] [Module.Finite ℤ G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ G
  let b := Module.Free.chooseBasis ℤ G
  have : Finite ι := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  let : DecidableEq ι := Classical.decEq ι
  let e : G ≃+ (ι →₀ ℤ) := b.repr.toAddEquiv
  exact PairCoeffLowerBound.exists_of_addEquiv e
    (exists_finsupp_pairCoeffLowerBound
      (B.map (PairCoeffLowerBound.addEquivEmbedding e)) hM)

lemma exists_fg_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G] [AddGroup.FG G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  have : Module.Finite ℤ G :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG G)
  have : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'
  exact exists_free_finite_pairCoeffLowerBound B hM

lemma exists_torsionFree_pairCoeffLowerBound
    [IsAddTorsionFree G]
    (B : Finset G) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset G, Q.Nonempty ∧ PairCoeffLowerBound Q B M := by
  classical
  let H : AddSubgroup G := AddSubgroup.closure (B : Set G)
  let BH : Finset H := B.subtype fun x => x ∈ H
  have : IsAddTorsionFree H := by
    constructor
    intro n hn x y hxy
    ext
    exact IsAddTorsionFree.nsmul_right_injective hn (by
      simpa using congrArg Subtype.val hxy)
  have : Finite (B : Set G) := Set.finite_coe_iff.mpr B.finite_toSet
  have : AddGroup.FG H := AddGroup.closure_finite_fg (B : Set G)
  obtain ⟨QH, hQH, hboundH⟩ :=
    exists_fg_torsionFree_pairCoeffLowerBound (G := H) BH hM
  let emb := PairCoeffLowerBound.addMonoidHomEmbedding
    H.subtype (AddSubgroup.subtype_injective H)
  have hBmap : BH.map emb = B := by
    ext γ
    simp only [Finset.mem_map, Subtype.exists]
    constructor
    · rintro ⟨a, haH, haBH, hγ⟩
      rw [← hγ]
      simpa [BH, emb, PairCoeffLowerBound.addMonoidHomEmbedding] using haBH
    · intro hγ
      exact ⟨γ, AddSubgroup.subset_closure hγ, by simpa [BH], rfl⟩
  refine ⟨QH.map emb, ?_, ?_⟩
  · rcases hQH with ⟨q, hq⟩
    exact ⟨q, Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  · have hmap :=
      PairCoeffLowerBound.map_addMonoidHom_of_injective
        H.subtype (AddSubgroup.subtype_injective H) hboundH
    simpa [emb, hBmap] using hmap

end FreeFinite

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma exists_pairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q.Nonempty ∧ PairCoeffLowerBound Q B M :=
  exists_torsionFree_pairCoeffLowerBound (G := E.Group) B hM

lemma exists_pairCoeffLowerBound_nonempty_ne
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ PairCoeffLowerBound Q B M := by
  classical
  obtain ⟨Q, hQ, hbound⟩ :=
    E.exists_pairCoeffLowerBound B hM
  exact ⟨Q, Finset.nonempty_iff_ne_empty.mp hQ, hbound⟩

lemma exists_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (B : Finset E.Group) {M : ℝ} (hM : 0 < M) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M := by
  simpa [FejerPairCoeffLowerBound] using
    E.exists_pairCoeffLowerBound_nonempty_ne B hM

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/ContinuousEndpoint.lean
    ============================================================= -/

/-
Erdős Problem 42 — Layer 1 continuous-analogue lemma.

Following Tao's May 2026 forum comment + natso26's clean exposition
(`fourier_positive_ulam_note.pdf`). The geometric core
`closed_proper_subgroup_haar_null` is proved here assumption-free; the main
`tao_continuous_avoidance` lemma is also proved once the standard measurable
group assumptions needed by Mathlib's Haar shear lemmas are available.

This file is shared scaffolding: Route A (Fourier-positive) eventually uses it
as the continuous endpoint of the U²-regularity / counting argument. Route B
(compact Cayley) uses a closely related lemma in its clique-forcing proof
(Lemma 2.7 of the compact Cayley PDF), which is also a candidate destination
for `closed_proper_subgroup_haar_null` once we open that black box.
-/
namespace Erdos42

open Filter Set Finset MeasureTheory
open scoped Pointwise Topology

universe u

/-- A nonnegative integrable real-valued function that is positive almost
everywhere on a probability space has positive integral. -/
lemma integral_pos_of_ae_pos_of_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {F : α → ℝ} (hFint : Integrable F μ)
    (hFnonneg : 0 ≤ᵐ[μ] F) (hFpos : ∀ᵐ x ∂μ, 0 < F x) :
    0 < ∫ x, F x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg_ae hFnonneg hFint]
  have hsupp_ae : ∀ᵐ x ∂μ, x ∈ Function.support F := by
    filter_upwards [hFpos] with x hx
    exact ne_of_gt hx
  have hcompl_zero : μ (Function.support F)ᶜ = 0 := by
    rwa [ae_iff] at hsupp_ae
  by_contra hnot
  have hsupp_zero : μ (Function.support F) = 0 := by
    exact le_antisymm (not_lt.mp hnot) bot_le
  have h_univ_zero : μ (Set.univ : Set α) = 0 := by
    have hcover : (Set.univ : Set α) =
        Function.support F ∪ (Function.support F)ᶜ := by
      ext x
      simp
    refine le_antisymm ?_ bot_le
    calc
      μ (Set.univ : Set α) =
          μ (Function.support F ∪ (Function.support F)ᶜ) := by rw [hcover]
      _ ≤ μ (Function.support F) + μ (Function.support F)ᶜ :=
          measure_union_le _ _
      _ = 0 := by simp [hsupp_zero, hcompl_zero]
  have h_univ_one : μ (Set.univ : Set α) = 1 := measure_univ
  norm_num [h_univ_one] at h_univ_zero

/-- Edge set of `K_M`, oriented by the natural order. This is the continuous
analogue of the finite ordered-clique product in the compact-Cayley proof. -/
def continuousCliqueEdgePairs (M : ℕ) : Finset (Fin M × Fin M) :=
  (Finset.univ : Finset (Fin M × Fin M)).filter (fun e => e.1 < e.2)

/-- Product kernel for the continuous `K_M` Cayley density. -/
noncomputable def continuousCliqueKernel
    {G : Type u} [Sub G] (M : ℕ) (f : G → ℝ) (x : Fin M → G) : ℝ :=
  ∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)

/-- Continuous Cayley `K_M` density associated to a kernel `f`. -/
noncomputable def continuousCliqueDensity
    {G : Type u} [MeasurableSpace G] [Sub G]
    (μ : Measure G) (M : ℕ) (f : G → ℝ) : ℝ :=
  ∫ x : Fin M → G, continuousCliqueKernel M f x ∂Measure.pi (fun _ : Fin M => μ)

lemma abs_prod_sub_prod_le_sum_abs_mul_two_pow
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf_abs : ∀ i ∈ s, |f i| ≤ 2)
    (hg_abs : ∀ i ∈ s, |g i| ≤ 2) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card := by
  classical
  revert hf_abs hg_abs
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih hf_abs hg_abs
    have hf_abs_s : ∀ i ∈ s, |f i| ≤ 2 := by
      intro i hi
      exact hf_abs i (by simp [hi])
    have hg_abs_s : ∀ i ∈ s, |g i| ≤ 2 := by
      intro i hi
      exact hg_abs i (by simp [hi])
    have htail := ih hf_abs_s hg_abs_s
    let Pf : ℝ := ∏ i ∈ s, f i
    let Pg : ℝ := ∏ i ∈ s, g i
    have hfa_abs : |f a| ≤ 2 := hf_abs a (by simp [ha])
    have hPg_abs : |Pg| ≤ (2 : ℝ) ^ s.card := by
      dsimp [Pg]
      rw [abs_prod]
      calc
        ∏ i ∈ s, |g i| ≤ ∏ _i ∈ s, (2 : ℝ) := by
          exact Finset.prod_le_prod
            (fun i _hi => abs_nonneg (g i))
            (fun i hi => hg_abs_s i hi)
        _ = (2 : ℝ) ^ s.card := by simp
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ s.card := by positivity
    have hpow_succ_ge : (2 : ℝ) ^ s.card ≤ (2 : ℝ) ^ (insert a s).card := by
      rw [Finset.card_insert_of_notMem ha]
      rw [pow_succ]
      nlinarith [show 0 ≤ (2 : ℝ) ^ s.card by positivity]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hdecomp : f a * Pf - g a * Pg =
        f a * (Pf - Pg) + (f a - g a) * Pg := by ring
    calc
      |f a * Pf - g a * Pg|
          = |f a * (Pf - Pg) + (f a - g a) * Pg| := by rw [hdecomp]
      _ ≤ |f a * (Pf - Pg)| + |(f a - g a) * Pg| := abs_add_le _ _
      _ = |f a| * |Pf - Pg| + |f a - g a| * |Pg| := by
            rw [abs_mul, abs_mul]
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ s.card) := by
            exact add_le_add
              (mul_le_mul hfa_abs htail (abs_nonneg _) zero_le_two)
              (mul_le_mul_of_nonneg_left hPg_abs (abs_nonneg _))
      _ ≤ 2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card) +
            |f a - g a| * ((2 : ℝ) ^ (insert a s).card) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hpow_succ_ge (abs_nonneg _))
                (2 * ((∑ i ∈ s, |f i - g i|) * (2 : ℝ) ^ s.card))
      _ = (|f a - g a| + ∑ i ∈ s, |f i - g i|) *
            (2 : ℝ) ^ (insert a s).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]
            ring

lemma abs_continuousCliqueKernel_sub_le_card_mul_two_pow
    {G : Type u} [Sub G] (M : ℕ) {f g : G → ℝ} {δ : ℝ}
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hclose : ∀ x, |f x - g x| ≤ δ)
    (x : Fin M → G) :
    |continuousCliqueKernel M f x - continuousCliqueKernel M g x| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  unfold continuousCliqueKernel
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
    positivity
  calc
    |(∏ e ∈ continuousCliqueEdgePairs M, f (x e.1 - x e.2)) -
        ∏ e ∈ continuousCliqueEdgePairs M, g (x e.1 - x e.2)|
        ≤ (∑ e ∈ continuousCliqueEdgePairs M,
            |f (x e.1 - x e.2) - g (x e.1 - x e.2)|) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact abs_prod_sub_prod_le_sum_abs_mul_two_pow
            (continuousCliqueEdgePairs M)
            (fun e => f (x e.1 - x e.2))
            (fun e => g (x e.1 - x e.2))
            (fun e _he => hf_abs _)
            (fun e _he => hg_abs _)
    _ ≤ (∑ _e ∈ continuousCliqueEdgePairs M, δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
          exact mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum fun e _he => hclose (x e.1 - x e.2))
            hpow_nonneg
    _ = (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp

lemma continuousCliqueDensity_lipschitz_sup_two_pow
    {G : Type u} [MeasurableSpace G] [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] (M : ℕ)
    {f g : G → ℝ} {δ : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_abs : ∀ x, |f x| ≤ 2)
    (hg_abs : ∀ x, |g x| ≤ 2)
    (hδ_nonneg : 0 ≤ δ)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |continuousCliqueDensity μ M f - continuousCliqueDensity μ M g| ≤
      (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
        (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  let Kf : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M f x
  let Kg : (Fin M → G) → ℝ := fun x => continuousCliqueKernel M g x
  have hKf_meas : Measurable Kf := by
    dsimp [Kf, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hKg_meas : Measurable Kg := by
    dsimp [Kg, continuousCliqueKernel]
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hg_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  let B : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hKf_bound : ∀ᵐ x ∂μM, ‖Kf x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kf, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |f (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (f (x e.1 - x e.2)))
                (fun e _he => hf_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKg_bound : ∀ᵐ x ∂μM, ‖Kg x‖ ≤ B := by
    exact Eventually.of_forall fun x => by
      dsimp [Kg, continuousCliqueKernel, B]
      rw [abs_prod]
      calc
        ∏ e ∈ continuousCliqueEdgePairs M, |g (x e.1 - x e.2)|
            ≤ ∏ _e ∈ continuousCliqueEdgePairs M, (2 : ℝ) := by
              exact Finset.prod_le_prod
                (fun e _he => abs_nonneg (g (x e.1 - x e.2)))
                (fun e _he => hg_abs _)
        _ = (2 : ℝ) ^ (continuousCliqueEdgePairs M).card := by simp
  have hKf_int : Integrable Kf μM :=
    Integrable.of_bound hKf_meas.aestronglyMeasurable B hKf_bound
  have hKg_int : Integrable Kg μM :=
    Integrable.of_bound hKg_meas.aestronglyMeasurable B hKg_bound
  let C : ℝ := (((continuousCliqueEdgePairs M).card : ℝ) * δ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs M).card
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ_nonneg) (by positivity)
  have hdiff_bound : ∀ᵐ x ∂μM, ‖Kf x - Kg x‖ ≤ C := by
    exact Eventually.of_forall fun x => by
      simpa [Kf, Kg, C, Real.norm_eq_abs] using
        abs_continuousCliqueKernel_sub_le_card_mul_two_pow M
          hf_abs hg_abs hclose x
  have hμM_real : μM.real Set.univ = 1 := by
    have : IsProbabilityMeasure μM := inferInstance
    simp [Measure.real, IsProbabilityMeasure.measure_univ]
  unfold continuousCliqueDensity
  change |∫ x, Kf x ∂μM - ∫ x, Kg x ∂μM| ≤ C
  rw [← integral_sub hKf_int hKg_int]
  calc
    |∫ x, Kf x - Kg x ∂μM|
        = ‖∫ x, Kf x - Kg x ∂μM‖ := by
            simp [Real.norm_eq_abs]
    _ ≤ C * μM.real Set.univ :=
        MeasureTheory.norm_integral_le_of_norm_le_const hdiff_bound
    _ = C := by rw [hμM_real, mul_one]

/-- If the continuous clique kernel is strictly positive on a nonempty open box,
then its continuous Cayley density is strictly positive.

This is the topological-measure endpoint for the `g(0) < 1` case of the compact
Cayley clique-forcing lemma: continuity gives a small open neighbourhood on
which every clique edge receives positive weight, and Haar open-positivity turns
that box into positive measure. -/
theorem continuousCliqueDensity_pos_of_pos_on_open_pi
    {G : Type u} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Sub G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (U : Set G) (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hposU : ∀ x : Fin M → G, x ∈ Set.univ.pi (fun _ : Fin M => U) →
      0 < continuousCliqueKernel M f x) :
    0 < continuousCliqueDensity μ M f := by
  let μM : Measure (Fin M → G) := Measure.pi (fun _ : Fin M => μ)
  have hkernel_meas : Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[μM] (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂μM, ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int : Integrable (fun x : Fin M → G => continuousCliqueKernel M f x) μM :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hpi_pos : 0 < μM (Set.univ.pi (fun _ : Fin M => U)) := by
    dsimp [μM]
    rw [Measure.pi_pi]
    rw [pos_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr
      (fun i _hi => ne_of_gt (hUopen.measure_pos μ hUnonempty))
  have hpi_subset_support :
      Set.univ.pi (fun _ : Fin M => U) ⊆
        Function.support (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    intro x hx
    exact ne_of_gt (hposU x hx)
  have hsupport_pos :
      0 < μM (Function.support (fun x : Fin M → G => continuousCliqueKernel M f x)) :=
    lt_of_lt_of_le hpi_pos (measure_mono hpi_subset_support)
  rw [continuousCliqueDensity]
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg_ae hkernel_nonneg hkernel_int).mpr
    hsupport_pos

/-- Compact-Cayley Lemma 2.7, open-neighbourhood case. If the continuous
allowed kernel is positive at zero, then it is positive on a small open
neighbourhood of zero. Shrinking the neighbourhood in the two coordinates makes
every clique edge difference land there, so the continuous `K_M` density is
positive.

This proves the `g(0) < 1` branch after setting `f = 1 - g`. -/
theorem continuousCliqueDensity_pos_of_pos_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (f : G → ℝ) (hf_cont : Continuous f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (hzero : 0 < f 0) :
    0 < continuousCliqueDensity μ M f := by
  let V : Set G := {x | 0 < f x}
  have hVopen : IsOpen V := by
    exact isOpen_lt continuous_const hf_cont
  have hVmem : V ∈ 𝓝 (0 : G) := hVopen.mem_nhds hzero
  have hVmem' : V ∈ 𝓝 (((0 : G), (0 : G)).1 - ((0 : G), (0 : G)).2) := by
    simpa using hVmem
  have hpre : (fun z : G × G => z.1 - z.2) ⁻¹' V ∈ 𝓝 ((0 : G), (0 : G)) := by
    convert (continuous_fst.sub continuous_snd).continuousAt hVmem' using 1
    rfl
  rcases mem_nhds_prod_iff'.mp hpre with
    ⟨U₁, U₂, hU₁open, hU₁zero, hU₂open, hU₂zero, hUsub⟩
  let U : Set G := U₁ ∩ U₂
  have hUopen : IsOpen U := hU₁open.inter hU₂open
  have hUnonempty : U.Nonempty := ⟨0, hU₁zero, hU₂zero⟩
  refine continuousCliqueDensity_pos_of_pos_on_open_pi μ M f hf_cont.measurable hf_nonneg
    hf_le U hUopen hUnonempty ?_
  intro x hx
  unfold continuousCliqueKernel
  refine Finset.prod_pos ?_
  intro e he
  have hx₁ : x e.1 ∈ U := hx e.1 (by simp)
  have hx₂ : x e.2 ∈ U := hx e.2 (by simp)
  have hpair : (x e.1, x e.2) ∈ U₁ ×ˢ U₂ := ⟨hx₁.1, hx₂.2⟩
  exact hUsub hpair

/-- A closed proper subgroup of a connected compact abelian Hausdorff group is
Haar-null. Geometric core of Layer 1; no Fourier content.

Argument: assume `μ H ≠ 0`. The cosets of `H` partition `G`, each with the same
measure `μ H` by translation invariance. With finite total measure and a
constant positive contribution, only finitely many cosets exist; hence
`H.FiniteIndex`. A closed finite-index subgroup is open
(`AddSubgroup.isOpen_of_isClosed_of_finiteIndex`). A non-empty clopen subset of
a connected space is the whole space, contradicting `H` proper. -/
theorem closed_proper_subgroup_haar_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_proper : (H : Set G) ≠ Set.univ) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  have hH_findex : H.FiniteIndex := hs.finite_left_iff.mp hs_finite
  have hH_open : IsOpen (H : Set G) :=
    AddSubgroup.isOpen_of_isClosed_of_finiteIndex H hH_closed
  exact hH_proper (IsClopen.eq_univ ⟨hH_closed, hH_open⟩ ⟨0, H.zero_mem⟩)

/-- A closed subgroup of infinite index is Haar-null.

This is the finite-index half of `closed_proper_subgroup_haar_null`, isolated
for compact duals where proving connectedness is overkill. Positive Haar
measure for `H` forces only finitely many cosets by the same disjoint-coset
counting argument used above. -/
theorem closed_subgroup_haar_null_of_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_not_finiteIndex : ¬ H.FiniteIndex) :
    μ (H : Set G) = 0 := by
  by_contra hμH_ne
  have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
  obtain ⟨s, hs, _⟩ := H.exists_isComplement_left 0
  have hs_finite : Finite s := by
    rcases finite_or_infinite s with hfin | hinf
    · exact hfin
    · exfalso
      let e : ℕ ↪ s := Infinite.natEmbedding s
      let f : ℕ → Set G := fun n => (e n).val +ᵥ (H : Set G)
      have h_disjoint : Pairwise (fun m n : ℕ => Disjoint (f m) (f n)) := by
        intro m n hmn
        have : (e m).val ≠ (e n).val :=
          fun h => hmn (e.injective (Subtype.ext h))
        exact hs.pairwiseDisjoint_vadd (e m).2 (e n).2 this
      have h_meas : ∀ n : ℕ, MeasurableSet (f n) :=
        fun n => hH_meas.const_vadd _
      have h_const : ∀ n : ℕ, μ (f n) = μ (H : Set G) :=
        fun n => measure_vadd μ (e n).val _
      have h_subset : (⋃ n : ℕ, f n) ⊆ Set.univ := fun _ _ => trivial
      have hμ_iUnion : μ (⋃ n : ℕ, f n) = ∑' n : ℕ, μ (f n) :=
        measure_iUnion h_disjoint h_meas
      have h_top : (∑' _ : ℕ, μ (H : Set G)) = ⊤ :=
        ENNReal.tsum_const_eq_top_of_ne_zero hμH_ne
      have hμ_top : μ (⋃ n : ℕ, f n) = ⊤ := by
        rw [hμ_iUnion, tsum_congr h_const]; exact h_top
      have hμ_univ_top : μ (Set.univ : Set G) = ⊤ :=
        top_unique (hμ_top ▸ measure_mono h_subset)
      exact absurd hμ_univ_top (ne_of_lt IsFiniteMeasure.measure_univ_lt_top)
  exact hH_not_finiteIndex (hs.finite_left_iff.mp hs_finite)

/-- If `H` is Haar-null, then the set of finite tuples whose `i,j` difference
lands in `H` is null. This is the Fubini/shear step used in Tao's continuous
avoidance lemma.

The proof splits off the `i`-th coordinate, evaluates the `j`-th coordinate in
the remaining product, and then uses the Haar-preserving shear
`(x, y) ↦ (x - y, y)` on `G × G`. -/
theorem pi_pair_sub_mem_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    {M : ℕ} (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hμH : μ (H : Set G) = 0)
    (i j : Fin M) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin M => μ)
      {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
  cases M with
  | zero =>
      exact Fin.elim0 i
  | succ n =>
      obtain ⟨k, hk⟩ :=
        Fin.exists_succAbove_eq (x := j) (y := i) (by simpa [ne_comm] using hij)
      have hsplit :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) i)
            (Measure.pi (fun _ : Fin (n + 1) => μ))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
        simpa using
          (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => G)
            (fun _ : Fin (n + 1) => μ) i)
      have hrest :
          MeasurePreserving (Function.eval k)
            (Measure.pi (fun _ : Fin n => μ)) μ :=
        measurePreserving_eval (fun _ : Fin n => μ) k
      have hpair_after :
          MeasurePreserving
            (Prod.map (fun x : G => x) (Function.eval k))
            (μ.prod (Measure.pi (fun _ : Fin n => μ))) (μ.prod μ) :=
        MeasurePreserving.prod
          (MeasurePreserving.id μ : MeasurePreserving (fun x : G => x) μ μ) hrest
      have hpair :
          MeasurePreserving (fun x : Fin (n + 1) → G => (x i, x j))
            (Measure.pi (fun _ : Fin (n + 1) => μ)) (μ.prod μ) := by
        convert hpair_after.comp hsplit using 1
        ext x
        · simp
        · rw [← hk]
          rfl
      have hdiff_prod :
          MeasurePreserving (fun z : G × G => (z.1 - z.2, z.2))
            (μ.prod μ) (μ.prod μ) := by
        simpa using (measurePreserving_sub_prod (μ := μ) (ν := μ))
      have hdiff :
          MeasurePreserving (fun z : G × G => z.1 - z.2)
            (μ.prod μ) μ := by
        simpa [Function.comp_def] using
          (measurePreserving_fst (μ := μ) (ν := μ)).comp hdiff_prod
      have hmap :
          MeasurePreserving (fun x : Fin (n + 1) → G => x i - x j)
            (Measure.pi (fun _ : Fin (n + 1) => μ)) μ := by
        simpa [Function.comp_def] using hdiff.comp hpair
      have hH_meas : MeasurableSet (H : Set G) := hH_closed.measurableSet
      calc
        Measure.pi (fun _ : Fin (n + 1) => μ)
            {x : Fin (n + 1) → G | x i - x j ∈ (H : Set G)}
            = (Measure.map (fun x : Fin (n + 1) → G => x i - x j)
                (Measure.pi (fun _ : Fin (n + 1) => μ))) (H : Set G) := by
              change Measure.pi (fun _ : Fin (n + 1) => μ)
                  ((fun x : Fin (n + 1) → G => x i - x j) ⁻¹' (H : Set G)) = _
              rw [Measure.map_apply hmap.measurable hH_meas]
        _ = μ (H : Set G) := by rw [hmap.map_eq]
        _ = 0 := hμH

/-- Compact-clique-forcing endpoint, case where the zero set is a proper
closed subgroup. If `f ≥ 0` and `f` vanishes exactly on such a subgroup, then
the continuous Cayley `K_M` density is strictly positive.

This is the measure-theoretic part of compact-Cayley Lemma 2.7 after the
Fourier/positive-definite argument has identified the level set
`{x | f x = 0}` as a proper closed subgroup. -/
theorem continuousCliqueDensity_pos_of_zeroLevel_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 0)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M f := by
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push Not at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  have hkernel_meas :
      Measurable (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    unfold continuousCliqueKernel
    refine (continuousCliqueEdgePairs M).measurable_prod ?_
    intro e _he
    exact hf_meas.comp ((measurable_pi_apply e.1).sub (measurable_pi_apply e.2))
  have hkernel_nonneg :
      0 ≤ᵐ[Measure.pi (fun _ : Fin M => μ)]
        (fun x : Fin M → G => continuousCliqueKernel M f x) := by
    exact Eventually.of_forall fun x => by
      unfold continuousCliqueKernel
      exact Finset.prod_nonneg fun e _he => hf_nonneg _
  have hkernel_bound :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        ‖continuousCliqueKernel M f x‖ ≤ 1 := by
    exact Eventually.of_forall fun x => by
      have hnonneg : 0 ≤ continuousCliqueKernel M f x := by
        unfold continuousCliqueKernel
        exact Finset.prod_nonneg fun e _he => hf_nonneg _
      have hle : continuousCliqueKernel M f x ≤ 1 := by
        unfold continuousCliqueKernel
        exact Finset.prod_le_one (fun e _he => hf_nonneg _) (fun e _he => hf_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hkernel_int :
      Integrable (fun x : Fin M → G => continuousCliqueKernel M f x)
        (Measure.pi (fun _ : Fin M => μ)) :=
    Integrable.of_bound hkernel_meas.aestronglyMeasurable 1 hkernel_bound
  have hkernel_pos :
      ∀ᵐ x ∂Measure.pi (fun _ : Fin M => μ),
        0 < continuousCliqueKernel M f x := by
    filter_upwards [h_ae_avoid] with x hx
    unfold continuousCliqueKernel
    refine Finset.prod_pos ?_
    intro e he
    have hlt : e.1 < e.2 := (Finset.mem_filter.mp he).2
    have hnot : x e.1 - x e.2 ∉ (H : Set G) := hx e.1 e.2 hlt
    have hne : f (x e.1 - x e.2) ≠ 0 := by
      intro hzero
      exact hnot ((hH_eq (x e.1 - x e.2)).mpr hzero)
    exact lt_of_le_of_ne (hf_nonneg _) hne.symm
  exact integral_pos_of_ae_pos_of_nonneg
    (Measure.pi (fun _ : Fin M => μ)) hkernel_int hkernel_nonneg hkernel_pos

/-- Compact-Cayley Lemma 2.7 endpoint after the positive-definite argument has
identified the level set `{x | g x = 1}` as a Haar-null closed subgroup.
Applying the zero-level null-subgroup theorem to `f = 1 - g` gives positive
continuous clique density for the allowed kernel. -/
theorem continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_meas : Measurable g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ g x = 1)
    (hμH : μ (H : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_zeroLevel_null_subgroup μ M
    (fun x => 1 - g x) ?_ ?_ ?_ H hH_closed ?_ hμH
  · exact measurable_const.sub hg_meas
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · intro x
    constructor
    · intro hx
      have hg : g x = 1 := (hH_eq x).mp hx
      linarith
    · intro hzero
      exact (hH_eq x).mpr (by linarith)

/-- **Tao's continuous-analogue key lemma (May 2026 forum comment).** Let `G` be a
connected compact abelian Hausdorff group with Haar probability measure `μ`, and
let `f : G → ℝ` be measurable with `f ≤ 1` pointwise. Suppose the level set
`{x : f x = 1}` coincides with a closed subgroup `H ≤ G`, and `H` is proper.
Then for almost every `(x₁, …, x_M) ∈ G^M`, `f (x_i − x_j) < 1` for all
`1 ≤ i < j ≤ M`.

The hypothesis "level set is a closed subgroup" is what positive-definiteness of
`f` is used to establish in the original argument; we factor it out so the core
lemma is purely measure-theoretic. -/
theorem tao_continuous_avoidance
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [ConnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (f : G → ℝ) (_hf_meas : Measurable f) (hf_le : ∀ x, f x ≤ 1)
    (H : AddSubgroup G) (hH_closed : IsClosed (H : Set G))
    (hH_eq : ∀ x : G, x ∈ H ↔ f x = 1)
    (hH_proper : (H : Set G) ≠ Set.univ) :
    ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → f (x i - x j) < 1 := by
  have hμH : μ (H : Set G) = 0 :=
    closed_proper_subgroup_haar_null μ H hH_closed hH_proper
  -- Fubini step (deferred): for each pair `(i, j)` with `i ≠ j`, the set of
  -- M-tuples with `x i - x j ∈ H` has product measure zero. Argument:
  -- translation invariance of `μ` plus `μ ↑H = 0` plus Fubini on the pi
  -- measure (or a measure-preserving "shear" change of variables).
  have h_pair_null :
      ∀ i j : Fin M, i ≠ j →
        Measure.pi (fun _ : Fin M => μ)
          {x : Fin M → G | x i - x j ∈ (H : Set G)} = 0 := by
    intro i j hij
    exact pi_pair_sub_mem_null μ H hH_closed hμH i j hij
  have h_bad_null :
      Measure.pi (fun _ : Fin M => μ)
        (⋃ (i : Fin M) (j : Fin M) (_ : i < j),
          {x : Fin M → G | x i - x j ∈ (H : Set G)}) = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
    by_cases hij : i < j
    · simp only [hij, Set.iUnion_true]
      exact h_pair_null i j (ne_of_lt hij)
    · simp only [hij, Set.iUnion_of_empty, measure_empty]
  have h_ae_avoid : ∀ᵐ (x : Fin M → G) ∂(Measure.pi (fun _ : Fin M => μ)),
      ∀ i j : Fin M, i < j → x i - x j ∉ (H : Set G) := by
    rw [ae_iff]
    refine measure_mono_null ?_ h_bad_null
    intro x hx
    push Not at hx
    obtain ⟨i, j, hij, hmem⟩ := hx
    exact Set.mem_iUnion.mpr
      ⟨i, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hij, hmem⟩⟩⟩
  filter_upwards [h_ae_avoid] with x hx i j hij
  have h_ne_one : f (x i - x j) ≠ 1 := by
    intro heq
    exact hx i j hij ((hH_eq (x i - x j)).mpr heq)
  exact lt_of_le_of_ne (hf_le _) h_ne_one

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/PositiveDefinite.lean
    ============================================================= -/

/-
Erdős Problem 42 — compact-Cayley route, positive-definite endpoint interface.

In compact-Cayley Lemma 2.7, the Fourier/positive-definite argument is used to
show that the level set `{x | g x = 1}` is a proper closed subgroup.  This file
formalizes the downstream subgroup construction and density conclusion from the
exact closure property that the positive-definite argument must supply.

No new assumption is introduced here: the remaining Route B work is to derive
`LevelOneSubgroupKernel g` from the compact limit's positive Fourier
coefficients.
-/

namespace Erdos42

open MeasureTheory

universe u

/-- Compact-Cayley Lemma 2.7, first branch. If `g 0 < 1`, then the allowed
kernel `1 - g` is positive at zero, hence has positive continuous clique
density by the open-neighbourhood endpoint. -/
theorem continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg0 : g 0 < 1) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  refine continuousCliqueDensity_pos_of_pos_at_zero μ M (fun x => 1 - g x)
    (continuous_const.sub hg_cont) ?_ ?_ ?_
  · intro x
    linarith [hg_le x]
  · intro x
    linarith [hg_nonneg x]
  · linarith

/-- Abstract output of the positive-definite part of compact-Cayley Lemma 2.7:
the level-one set is nonempty and closed under subtraction.

For the eventual full proof, this structure should be produced from the
positive-definite kernel attached to `g`. -/
structure LevelOneSubgroupKernel {G : Type u} [Zero G] [Sub G]
    (g : G → ℝ) : Prop where
  map_zero : g 0 = 1
  sub_mem : ∀ x y : G, g x = 1 → g y = 1 → g (x - y) = 1

/-- The subgroup `{x | g x = 1}` built from the level-one closure property. -/
def levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    (g : G → ℝ) (hg : LevelOneSubgroupKernel g) : AddSubgroup G where
  carrier := {x | g x = 1}
  zero_mem' := hg.map_zero
  add_mem' := by
    intro x y hx hy
    have hneg_y : g (-y) = 1 := by
      simpa using hg.sub_mem 0 y hg.map_zero hy
    simpa [sub_eq_add_neg] using hg.sub_mem x (-y) hx hneg_y
  neg_mem' := by
    intro x hx
    simpa using hg.sub_mem 0 x hg.map_zero hx

lemma mem_levelOneAddSubgroup {G : Type u} [AddCommGroup G]
    {g : G → ℝ} {hg : LevelOneSubgroupKernel g} {x : G} :
    x ∈ levelOneAddSubgroup g hg ↔ g x = 1 := Iff.rfl

lemma levelOneAddSubgroup_isClosed {G : Type u}
    [AddCommGroup G] [TopologicalSpace G]
    {g : G → ℝ} (hg : LevelOneSubgroupKernel g)
    (hg_cont : Continuous g) :
    IsClosed (levelOneAddSubgroup g hg : Set G) := by
  change IsClosed (g ⁻¹' ({1} : Set ℝ))
  exact isClosed_singleton.preimage hg_cont

/-- Compact-Cayley endpoint with the exact null-subgroup hypothesis on the
level-one subgroup.  This avoids connectedness: once the positive-definite
argument gives subgroup closure and the compact-dual algebra gives nullness,
the measure-theoretic clique forcing is immediate. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hμH : μ ((levelOneAddSubgroup g hg_level : AddSubgroup G) : Set G) = 0) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  have hH_eq : ∀ x : G, x ∈ H ↔ g x = 1 := by
    intro x
    rfl
  exact continuousCliqueDensity_pos_of_one_sub_level_one_null_subgroup
    μ M g hg_cont.measurable hg_nonneg hg_le H hH_closed hH_eq hμH

/-- Compact-Cayley endpoint where nullness of the level-one subgroup is proved
from infinite index.  This is often a smaller target for the extraction compact
dual than proving connectedness of the whole dual group. -/
theorem continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hg_level : LevelOneSubgroupKernel g)
    (hH_not_finiteIndex :
      ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  let H : AddSubgroup G := levelOneAddSubgroup g hg_level
  have hH_closed : IsClosed (H : Set G) :=
    levelOneAddSubgroup_isClosed hg_level hg_cont
  exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_null μ M g
    hg_cont hg_nonneg hg_le hg_level
    (closed_subgroup_haar_null_of_not_finiteIndex μ H hH_closed hH_not_finiteIndex)

/-- Two-branch compact-Cayley endpoint using the narrower infinite-index
certificate instead of connectedness. -/
theorem continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
    {G : Type u} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSub₂ G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (M : ℕ)
    (g : G → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_le : ∀ x, g x ≤ 1)
    (hbranch :
      g 0 < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel g,
          ¬ (levelOneAddSubgroup g hg_level : AddSubgroup G).FiniteIndex) :
    0 < continuousCliqueDensity μ M (fun x => 1 - g x) := by
  rcases hbranch with hg0 | hlevel
  · exact continuousCliqueDensity_pos_of_one_sub_of_lt_one_at_zero μ M g hg_cont
      hg_nonneg hg_le hg0
  · rcases hlevel with ⟨hg_level, hnot⟩
    exact continuousCliqueDensity_pos_of_levelOneSubgroupKernel_not_finiteIndex
      μ M g hg_cont hg_nonneg hg_le hg_level hnot

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/LimitKernel.lean
    ============================================================= -/

/-
Erdős Problem 42 — first compact-limit kernel coefficient layer.

This file defines the complement coefficients
`gCoeff 0 = 1 - a(0).re`, `gCoeff γ = -a(γ).re` for nonzero `γ`, where
`a` is the extracted Cayley Fourier coefficient limit.  The summability and
continuous Fourier-series construction are later steps.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42 MeasureTheory
open scoped Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

lemma coeff_norm_le_one (E : CayleyExtraction S) (γ : E.Group) :
    ‖E.coeff γ‖ ≤ 1 := by
  have hlim :=
    (continuous_norm.tendsto (E.coeff γ)).comp (E.coeff_tendsto γ)
  have hbound :
      ∀ᶠ n in atTop,
        ‖(letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          normalizedDftCoeff (S.T (E.φ n)) (E.lift n γ))‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun n => by
      let : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
      simpa [CayleyCounterSeq.toFourierSeq, FourierSeq.coeff,
        normalizedDftCoeff] using
        (S.toFourierSeq).norm_coeff_le_one (E.φ n) (E.lift n γ))
  exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbound

lemma coeff_zero_re_le_one (E : CayleyExtraction S) :
    (E.coeff (0 : E.Group)).re ≤ 1 := by
  exact (Complex.re_le_norm (E.coeff (0 : E.Group))).trans
    (E.coeff_norm_le_one 0)

/-- Complement Fourier coefficients for the compact limit kernel `g = 1 - f`. -/
noncomputable def gCoeff (E : CayleyExtraction S) (γ : E.Group) : ℝ :=
  if γ = 0 then 1 - (E.coeff (0 : E.Group)).re else -(E.coeff γ).re

lemma gCoeff_zero (E : CayleyExtraction S) :
    E.gCoeff 0 = 1 - (E.coeff (0 : E.Group)).re := by
  simp [gCoeff]

lemma gCoeff_of_ne_zero (E : CayleyExtraction S)
    {γ : E.Group} (hγ : γ ≠ 0) :
    E.gCoeff γ = -(E.coeff γ).re := by
  simp [gCoeff, hγ]

lemma gCoeff_nonneg (E : CayleyExtraction S) (γ : E.Group) :
    0 ≤ E.gCoeff γ := by
  by_cases hγ : γ = 0
  · subst hγ
    rw [E.gCoeff_zero]
    linarith [E.coeff_zero_re_le_one]
  · rw [E.gCoeff_of_ne_zero hγ]
    exact neg_nonneg.mpr (E.coeff_nonpos_of_ne_zero hγ)

lemma gCoeff_zero_le_one_sub_eta (E : CayleyExtraction S) :
    E.gCoeff 0 ≤ 1 - η := by
  rw [E.gCoeff_zero]
  linarith [E.coeff_zero_ge_eta]

lemma one_sub_indicatorCoeffFunctional_fejer_re_le_one
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re ≤ 1 := by
  have htendsto :=
    E.finiteComplementFejerAverage_tendsto_one_sub_indicatorCoeffFunctional Q hQ
  have htendsto_re :=
    Complex.continuous_re.tendsto
      (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)) |>.comp htendsto
  exact le_of_tendsto_of_tendsto htendsto_re tendsto_const_nhds
    (E.finiteComplementFejerAverage_re_le_one_eventually Q hQ)

lemma one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅) :
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re =
      ∑ γ ∈ (E.fejerTrigPoly Q).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((P γ).re * E.gCoeff γ) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_im : (P γ).im = 0 := by
      simpa [P] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re : (P γ * E.coeff γ).re = (P γ).re * (E.coeff γ).re := by
      rw [Complex.mul_re, hP_im, hcoeff_im]
      ring
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hP0_re : (P (0 : E.Group)).re = 1 := by
        rw [hP0]
        simp
      rw [E.gCoeff_zero, hmul_re, hP0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
  calc
    (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.fejerTrigPoly Q).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ := by
            simp [P]

lemma shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re =
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  have hP0 : P (0 : E.Group) = 1 := by
    simpa [P, TrigPoly.compactAverage] using
      E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ
  have hK0 : K (0 : E.Group) = 1 := by
    simpa [K, TrigPoly.compactAverage] using
      E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
  have h0mem : (0 : E.Group) ∈ P.support := by
    rw [Finsupp.mem_support_iff]
    rw [hP0]
    norm_num
  have hindicator_re :
      (TrigPoly.indicatorCoeffFunctional P).re =
        ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
    unfold TrigPoly.indicatorCoeffFunctional
    rw [Finsupp.sum]
    simp [Complex.re_sum]
  have hsum_if :
      (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : E.Group)]
    · simp
    · intro γ hγ hγ_ne
      simp [hγ_ne]
    · intro hnot
      exact False.elim (hnot h0mem)
  have hpoint :
      ∀ γ ∈ P.support,
        ((K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re) =
          (if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re := by
    intro γ _hγ
    have hP_apply :
        P γ = K γ * E.addCharacterValue z γ := by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ
    have hK_im : (K γ).im = 0 := by
      simpa [K] using E.fejerTrigPoly_apply_im_eq_zero Q γ
    have hcoeff_im : (E.coeff γ).im = 0 := E.coeff_im_eq_zero γ
    have hmul_re :
        (P γ * E.coeff γ).re =
          (K γ).re * (E.addCharacterValue z γ).re * (E.coeff γ).re := by
      rw [hP_apply]
      simp [Complex.mul_re, Complex.mul_im, hK_im, hcoeff_im,
        mul_left_comm, mul_comm]
    by_cases hγ0 : γ = 0
    · subst hγ0
      have hK0_re : (K (0 : E.Group)).re = 1 := by
        rw [hK0]
        simp
      rw [E.gCoeff_zero, hmul_re, hK0_re]
      simp
    · rw [E.gCoeff_of_ne_zero hγ0, hmul_re]
      simp [hγ0]
      ring
  calc
    (TrigPoly.compactAverage (E.shiftedFejerTrigPoly Q z) -
        TrigPoly.indicatorCoeffFunctional (E.shiftedFejerTrigPoly Q z)).re
        = 1 - (TrigPoly.indicatorCoeffFunctional P).re := by
            simp [P, E.shiftedFejerTrigPoly_compactAverage_eq_one_of_nonempty Q z hQ]
    _ = (∑ γ ∈ P.support, if γ = (0 : E.Group) then (1 : ℝ) else 0) -
          ∑ γ ∈ P.support, (P γ * E.coeff γ).re := by
            rw [hsum_if, hindicator_re]
    _ = ∑ γ ∈ P.support,
          (((if γ = (0 : E.Group) then (1 : ℝ) else 0) -
            (P γ * E.coeff γ).re)) := by
            rw [Finset.sum_sub_distrib]
    _ = ∑ γ ∈ P.support,
          (K γ).re * E.gCoeff γ * (E.addCharacterValue z γ).re := by
            refine Finset.sum_congr rfl ?_
            intro γ hγ
            exact (hpoint γ hγ).symm
    _ = ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
          ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
            simp [P, K]

lemma sum_gCoeff_le_of_fejerCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff :
      ∀ γ ∈ B, 1 - M ≤ ((E.fejerTrigPoly Q) γ).re) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  let P : E.TrigPoly := E.fejerTrigPoly Q
  have hpos : 0 < 1 - M := by linarith
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hre_pos : 0 < (P γ).re := by
      exact lt_of_lt_of_le hpos (by simpa [P] using hcoeff γ hγ)
    by_contra hnot
    have hzero : P γ = 0 := Finsupp.notMem_support_iff.mp hnot
    rw [hzero] at hre_pos
    norm_num at hre_pos
  calc
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ)
        = ∑ γ ∈ B, (1 - M) * E.gCoeff γ := by
            rw [Finset.mul_sum]
    _ ≤ ∑ γ ∈ B, (P γ).re * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            exact mul_le_mul_of_nonneg_right
              (by simpa [P] using hcoeff γ hγ) (E.gCoeff_nonneg γ)
    _ ≤ ∑ γ ∈ P.support, (P γ).re * E.gCoeff γ := by
            exact Finset.sum_le_sum_of_subset_of_nonneg hBsupport (by
              intro γ _hγP _hγB
              exact mul_nonneg
                (by simpa [P] using E.fejerTrigPoly_apply_re_nonneg Q γ)
                (E.gCoeff_nonneg γ))
    _ = (1 - TrigPoly.indicatorCoeffFunctional (E.fejerTrigPoly Q)).re := by
            rw [E.one_sub_indicatorCoeffFunctional_fejer_re_eq_sum_gCoeff Q hQ]
    _ ≤ 1 := E.one_sub_indicatorCoeffFunctional_fejer_re_le_one Q hQ

lemma sum_gCoeff_le_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (hQ : Q ≠ ∅)
    {M : ℝ} (hM_lt : M < 1)
    (hcoeff : E.FejerPairCoeffLowerBound Q B M) :
    (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
  E.sum_gCoeff_le_of_fejerCoeffLowerBound Q B hQ hM_lt (by
    intro γ hγ
    rw [E.fejerTrigPoly_apply_re_eq_pairRatio Q γ]
    exact hcoeff γ hγ)

lemma sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M)
    (B : Finset E.Group) :
    (∑ γ ∈ B, E.gCoeff γ) ≤ 1 := by
  classical
  by_contra hnot
  have hsum_gt : 1 < ∑ γ ∈ B, E.gCoeff γ := lt_of_not_ge hnot
  let A : ℝ := ∑ γ ∈ B, E.gCoeff γ
  let M : ℝ := (A - 1) / (2 * A)
  have hA_pos : 0 < A := by
    exact lt_trans zero_lt_one hsum_gt
  have hM_pos : 0 < M := by
    dsimp [M]
    have hnum : 0 < A - 1 := by
      simpa [A] using sub_pos.mpr hsum_gt
    have hden : 0 < 2 * A := by positivity
    exact div_pos hnum hden
  have hM_lt : M < 1 := by
    dsimp [M]
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    field_simp [hA_ne]
    nlinarith [hA_pos]
  obtain ⟨Q, hQ, hlower⟩ := hfejer B M hM_pos
  have hbound :
      (1 - M) * (∑ γ ∈ B, E.gCoeff γ) ≤ 1 :=
    E.sum_gCoeff_le_of_fejerPairCoeffLowerBound Q B hQ hM_lt hlower
  have hprod_gt : 1 < (1 - M) * (∑ γ ∈ B, E.gCoeff γ) := by
    have hcalc : (1 - M) * A = (A + 1) / 2 := by
      dsimp [M]
      have hA_ne : A ≠ 0 := ne_of_gt hA_pos
      field_simp [hA_ne]
      ring
    have hA_gt : 1 < A := by simpa [A] using hsum_gt
    change 1 < (1 - M) * A
    rw [hcalc]
    nlinarith
  exact not_le_of_gt hprod_gt hbound

lemma summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    Summable E.gCoeff :=
  summable_of_sum_le (fun γ => E.gCoeff_nonneg γ)
    (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B)

lemma tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (E : CayleyExtraction S)
    (hfejer :
      ∀ (B : Finset E.Group) (M : ℝ), 0 < M →
        ∃ Q : Finset E.Group,
          Q ≠ ∅ ∧ E.FejerPairCoeffLowerBound Q B M) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 := by
  have hsum : Summable E.gCoeff :=
    E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound hfejer
  exact le_of_tendsto_of_tendsto hsum.hasSum tendsto_const_nhds
    (Filter.Eventually.of_forall
      (fun B => E.sum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound hfejer B))

lemma summable_gCoeff (E : CayleyExtraction S) :
    Summable E.gCoeff :=
  E.summable_gCoeff_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

lemma tsum_gCoeff_le_one (E : CayleyExtraction S) :
    (∑' γ : E.Group, E.gCoeff γ) ≤ 1 :=
  E.tsum_gCoeff_le_one_of_forall_fejerPairCoeffLowerBound
    (fun B _ hM => E.exists_fejerPairCoeffLowerBound B hM)

/-- Complex Fourier-series term for the complement kernel. -/
noncomputable def gComplexTerm
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) : ℂ :=
  (E.gCoeff γ : ℂ) * E.addCharacterValue z γ

/-- Complex Fourier series for the compact complement kernel.  The definition
is meaningful without proving summability, but all analytic use below is under
an explicit `Summable E.gCoeff` hypothesis. -/
noncomputable def gComplex
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℂ :=
  ∑' γ : E.Group, E.gComplexTerm γ z

/-- Real-valued compact complement kernel, obtained as the real part of the
complex Fourier series. -/
noncomputable def gReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  (E.gComplex z).re

/-- Allowed compact kernel `f = 1 - g`. -/
noncomputable def fReal
    (E : CayleyExtraction S) (z : E.CompactAddDual) : ℝ :=
  1 - E.gReal z

lemma norm_gComplexTerm_le_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ ≤ E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma norm_gComplexTerm_eq_gCoeff
    (E : CayleyExtraction S) (γ : E.Group) (z : E.CompactAddDual) :
    ‖E.gComplexTerm γ z‖ = E.gCoeff γ := by
  rw [gComplexTerm, norm_mul, E.norm_addCharacterValue]
  simp [Real.norm_eq_abs, abs_of_nonneg (E.gCoeff_nonneg γ)]

lemma gComplexTerm_continuous
    (E : CayleyExtraction S) (γ : E.Group) :
    Continuous (fun z : E.CompactAddDual => E.gComplexTerm γ z) := by
  exact continuous_const.mul (E.addCharacterValue_continuous γ)

lemma gComplex_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gComplex := by
  unfold gComplex
  exact continuous_tsum
    (fun γ => E.gComplexTerm_continuous γ)
    hsum
    (fun γ z => E.norm_gComplexTerm_le_gCoeff γ z)

lemma gReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.gReal :=
  Complex.continuous_re.comp (E.gComplex_continuous hsum)

lemma fReal_continuous
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff) :
    Continuous E.fReal :=
  continuous_const.sub (E.gReal_continuous hsum)

lemma gComplex_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gComplex (0 : E.CompactAddDual) =
      ((∑' γ : E.Group, E.gCoeff γ) : ℂ) := by
  unfold gComplex gComplexTerm
  simp

lemma gReal_zero_eq_tsum_gCoeff
    (E : CayleyExtraction S) :
    E.gReal (0 : E.CompactAddDual) =
      ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  rw [E.gComplex_zero_eq_tsum_gCoeff]
  rw [← Complex.ofReal_tsum (fun γ : E.Group => E.gCoeff γ)]
  simp

lemma addCharacterValue_re_le_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    (E.addCharacterValue z γ).re ≤ 1 := by
  exact (Complex.re_le_norm (E.addCharacterValue z γ)).trans
    (by simp)

lemma neg_one_le_addCharacterValue_re
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group) :
    -1 ≤ (E.addCharacterValue z γ).re := by
  have h_abs :
      |(E.addCharacterValue z γ).re| ≤ (1 : ℝ) := by
    simpa [E.norm_addCharacterValue z γ] using
      Complex.abs_re_le_norm (E.addCharacterValue z γ)
  exact (abs_le.mp h_abs).1

lemma shiftedFejer_weighted_gCoeff_character_sum_nonneg
    (E : CayleyExtraction S) (Q : Finset E.Group) (z : E.CompactAddDual)
    (hQ : Q ≠ ∅) :
    0 ≤
      ∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support,
        ((E.fejerTrigPoly Q) γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re := by
  have h := E.shiftedFejer_complementFunctional_re_nonneg Q z
  rwa [E.shiftedFejer_complementFunctional_re_eq_sum_gCoeff_mul_character_re
    Q z hQ] at h

lemma sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Q B : Finset E.Group) (z : E.CompactAddDual)
    {M : ℝ} (hQ : Q ≠ ∅) (hM_lt : M < 1)
    (hlower : E.FejerPairCoeffLowerBound Q B M) :
    - (∑ γ ∈ (E.shiftedFejerTrigPoly Q z).support \ B, E.gCoeff γ) -
        M * (∑ γ ∈ B, E.gCoeff γ) ≤
      ∑ γ ∈ B, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  classical
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let K : E.TrigPoly := E.fejerTrigPoly Q
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let w : E.Group → ℝ := fun γ => (K γ).re
  have hBsupport : B ⊆ P.support := by
    intro γ hγ
    have hratio :
        1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
      hlower γ hγ
    have hw_pos : 0 < w γ := by
      have hpos : 0 < 1 - M := by linarith
      exact lt_of_lt_of_le hpos (by
        simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using hratio)
    have hK_ne : K γ ≠ 0 := by
      intro hzero
      have : w γ = 0 := by simp [w, hzero]
      linarith
    have hchar_ne : E.addCharacterValue z γ ≠ 0 := by
      intro hzero
      have hnorm := E.norm_addCharacterValue z γ
      rw [hzero] at hnorm
      norm_num at hnorm
    rw [Finsupp.mem_support_iff]
    rw [show P γ = K γ * E.addCharacterValue z γ by
      simpa [P, K] using E.shiftedFejerTrigPoly_apply Q z γ]
    exact mul_ne_zero hK_ne hchar_ne
  have hweighted :
      0 ≤ ∑ γ ∈ P.support, w γ * a γ := by
    simpa [P, K, w, a, mul_assoc] using
      E.shiftedFejer_weighted_gCoeff_character_sum_nonneg Q z hQ
  have hsplit :
      ∑ γ ∈ P.support, w γ * a γ =
        (∑ γ ∈ P.support \ B, w γ * a γ) +
          ∑ γ ∈ B, w γ * a γ := by
    exact (Finset.sum_sdiff hBsupport).symm
  have htail_le :
      (∑ γ ∈ P.support \ B, w γ * a γ) ≤
        ∑ γ ∈ P.support \ B, E.gCoeff γ := by
    refine Finset.sum_le_sum ?_
    intro γ _hγ
    have hw_nonneg : 0 ≤ w γ := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_nonneg Q γ
    have hw_le_one : w γ ≤ 1 := by
      simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
    have ha_le : a γ ≤ E.gCoeff γ := by
      dsimp [a]
      simpa using
        mul_le_mul_of_nonneg_left
          (E.addCharacterValue_re_le_one z γ) (E.gCoeff_nonneg γ)
    have hwg_le : w γ * E.gCoeff γ ≤ E.gCoeff γ := by
      nlinarith [hw_nonneg, hw_le_one, E.gCoeff_nonneg γ]
    exact (mul_le_mul_of_nonneg_left ha_le hw_nonneg).trans hwg_le
  have hB_le :
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, a γ := by
    calc
      (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ)
          = ∑ γ ∈ B, (w γ * a γ - M * E.gCoeff γ) := by
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ ∑ γ ∈ B, a γ := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          have hratio :
              1 - M ≤ ((pairFiber Q γ).card : ℝ) / (Q.card : ℝ) :=
            hlower γ hγ
          have hw_lower : 1 - M ≤ w γ := by
            simpa [w, K, E.fejerTrigPoly_apply_re_eq_pairRatio Q γ] using
              hratio
          have hw_le_one : w γ ≤ 1 := by
            simpa [w, K] using E.fejerTrigPoly_apply_re_le_one Q γ
          have hone_minus_nonneg : 0 ≤ 1 - w γ := by linarith
          have hone_minus_le : 1 - w γ ≤ M := by linarith
          have ha_ge_neg : -E.gCoeff γ ≤ a γ := by
            dsimp [a]
            have hg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
            have hre := E.neg_one_le_addCharacterValue_re z γ
            calc
              -E.gCoeff γ = E.gCoeff γ * (-1) := by ring
              _ ≤ E.gCoeff γ * (E.addCharacterValue z γ).re :=
                  mul_le_mul_of_nonneg_left hre hg
          have herror :
              -M * E.gCoeff γ ≤ (1 - w γ) * a γ := by
            have hleft :
                -(1 - w γ) * E.gCoeff γ ≤ (1 - w γ) * a γ := by
              calc
                -(1 - w γ) * E.gCoeff γ
                    = (1 - w γ) * (-E.gCoeff γ) := by ring
                _ ≤ (1 - w γ) * a γ :=
                    mul_le_mul_of_nonneg_left ha_ge_neg hone_minus_nonneg
            have hright :
                -M * E.gCoeff γ ≤ -(1 - w γ) * E.gCoeff γ := by
              have hmul :
                  (1 - w γ) * E.gCoeff γ ≤ M * E.gCoeff γ :=
                mul_le_mul_of_nonneg_right hone_minus_le
                  (E.gCoeff_nonneg γ)
              linarith
            exact hright.trans hleft
          nlinarith
  have hB_lower :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) ≤
        ∑ γ ∈ B, w γ * a γ := by
    have hweighted_split :
        0 ≤ (∑ γ ∈ P.support \ B, w γ * a γ) +
              ∑ γ ∈ B, w γ * a γ := by
      simpa [hsplit] using hweighted
    linarith
  have hmain :
      - (∑ γ ∈ P.support \ B, E.gCoeff γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) ≤
        (∑ γ ∈ B, w γ * a γ) -
          M * (∑ γ ∈ B, E.gCoeff γ) := by
    linarith
  exact hmain.trans (by simpa [a] using hB_le)

lemma addCharacterValue_eq_one_of_re_eq_one
    (E : CayleyExtraction S) (z : E.CompactAddDual) (γ : E.Group)
    (hre : (E.addCharacterValue z γ).re = 1) :
    E.addCharacterValue z γ = 1 := by
  have hnormSq : Complex.normSq (E.addCharacterValue z γ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, E.norm_addCharacterValue]
    norm_num
  have him : (E.addCharacterValue z γ).im = 0 := by
    rw [Complex.normSq_apply, hre] at hnormSq
    nlinarith [sq_nonneg (E.addCharacterValue z γ).im]
  apply Complex.ext
  · simp [hre]
  · simp [him]

lemma summable_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    Summable fun γ : E.Group =>
      E.gCoeff γ * (E.addCharacterValue z γ).re := by
  refine hsum.of_norm_bounded ?_
  intro γ
  have hcoeff_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
  have hre_abs : |(E.addCharacterValue z γ).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
      (by simp)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoeff_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hre_abs hcoeff_nonneg]

lemma gReal_eq_tsum_gCoeff_mul_character_re
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z =
      ∑' γ : E.Group, E.gCoeff γ * (E.addCharacterValue z γ).re := by
  have hterm : Summable fun γ : E.Group => E.gComplexTerm γ z :=
    hsum.of_norm_bounded (fun γ => E.norm_gComplexTerm_le_gCoeff γ z)
  unfold gReal gComplex
  rw [Complex.re_tsum hterm]
  refine tsum_congr ?_
  intro γ
  simp [gComplexTerm, Complex.mul_re]

lemma fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff
    (E : CayleyExtraction S) (z : E.CompactAddDual) :
    E.fReal z =
      (E.coeff (0 : E.Group)).re -
        ∑' γ : E.Group,
          if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re := by
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsplit := hsumA.tsum_eq_add_tsum_ite (0 : E.Group)
  have hzero : a 0 = E.gCoeff 0 := by
    simp [a]
  unfold fReal
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  change 1 - (∑' γ : E.Group, a γ) =
    (E.coeff (0 : E.Group)).re -
      ∑' γ : E.Group, if γ = 0 then 0 else a γ
  rw [hsplit, hzero, E.gCoeff_zero]
  ring

lemma compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (A : Finset E.Group)
    (hA0 : (0 : E.Group) ∈ A)
    (hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A) :
    E.compactSmoothReal Q z =
      (E.coeff (0 : E.Group)).re -
        ∑ γ ∈ A,
          if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re := by
  classical
  rw [E.compactSmoothReal_eq_sum_of_support_subset Q z A hAsupport]
  let t : E.Group → ℝ :=
    fun γ => (E.fejerTrigPoly Q γ).re * (E.coeff γ).re *
      (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have ht0 : t 0 = (E.coeff (0 : E.Group)).re := by
    have hK0c : E.fejerTrigPoly Q (0 : E.Group) = 1 := by
      simpa [TrigPoly.compactAverage] using
        E.fejerTrigPoly_compactAverage_eq_one_of_nonempty Q hQ
    simp [t, hK0c]
  have ht_ne : ∀ γ ∈ A \ ({0} : Finset E.Group), t γ = -b γ := by
    intro γ hγ
    have hne : γ ≠ 0 := by
      intro hzero
      exact (Finset.mem_sdiff.mp hγ).2 (by simp [hzero])
    simp [t, b, hne, E.gCoeff_of_ne_zero hne, mul_assoc]
  have hsum_t :
      (∑ γ ∈ A, t γ) =
        (E.coeff (0 : E.Group)).re +
          ∑ γ ∈ A \ ({0} : Finset E.Group), -b γ := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hA0, ht0]
    congr 1
    exact Finset.sum_congr rfl ht_ne
  have hsum_b :
      (∑ γ ∈ A, b γ) =
        ∑ γ ∈ A \ ({0} : Finset E.Group), b γ := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hA0]
    simp [b]
  change (∑ γ ∈ A, t γ) =
    (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ
  rw [hsum_t, hsum_b]
  rw [Finset.sum_neg_distrib]
  ring

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
  classical
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  have ha_bound : ∀ γ : E.Group, ‖a γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hzero : γ = 0
    · simpa [a, hzero] using E.gCoeff_nonneg γ
    · have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
        (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
          (by simp [E.norm_addCharacterValue z γ])
      have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
      simpa [a, hzero, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hg_nonneg] using
        mul_le_of_le_one_right hg_nonneg hchar_abs
  have hsumA : Summable a := by
    exact E.summable_gCoeff.of_norm_bounded ha_bound
  have hsplit := hsumA.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑ γ ∈ A, a γ) - ∑' γ : E.Group, a γ =
        - ∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ := by
    rw [← hsplit]
    ring
  have hsub_g :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => E.gCoeff γ) :=
    E.summable_gCoeff.subtype _
  have hnorm_summable :
      Summable (fun γ : ↑((↑A : Set E.Group)ᶜ) => ‖a γ‖) := by
    refine hsub_g.of_norm_bounded ?_
    intro γ
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (a γ))] using
      ha_bound (γ : E.Group)
  have htail_norm :
      ‖∑' γ : ↑((↑A : Set E.Group)ᶜ), a γ‖ ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have htail_norm_le_g :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), ‖a γ‖) ≤
        ∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ := by
    refine Summable.tsum_le_tsum ?_ hnorm_summable hsub_g
    intro γ
    exact ha_bound (γ : E.Group)
  simpa [a, htail_eq, Real.norm_eq_abs] using htail_norm.trans htail_norm_le_g

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
  have htail :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_tsum_compl A z
  have hsplit := E.summable_gCoeff.sum_add_tsum_compl (s := A)
  have htail_eq :
      (∑' γ : ↑((↑A : Set E.Group)ᶜ), E.gCoeff γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ := by
    rw [← hsplit]
    ring
  simpa [htail_eq] using htail

lemma abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail
    (E : CayleyExtraction S) (A : Finset E.Group)
    (z : E.CompactAddDual) {δ : ℝ}
    (htail :
      |(∑ γ ∈ A, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |(∑ γ ∈ A,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      ∑' γ : E.Group,
        if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re| ≤ δ := by
  have h :=
    E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_gCoeff_tail A z
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ A, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp htail).1
    linarith
  exact h.trans htail_upper

lemma sum_gCoeff_sdiff_le_of_gCoeff_tail
    (E : CayleyExtraction S) (B A : Finset E.Group) {δ : ℝ}
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    (∑ γ ∈ A \ B, E.gCoeff γ) ≤ δ := by
  classical
  let c : E.Group → ℝ := fun γ => if γ ∈ B then 0 else E.gCoeff γ
  have hc_nonneg : ∀ γ, 0 ≤ c γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ]
    · simp [c, hγ, E.gCoeff_nonneg γ]
  have hc_bound : ∀ γ, ‖c γ‖ ≤ E.gCoeff γ := by
    intro γ
    by_cases hγ : γ ∈ B
    · simp [c, hγ, E.gCoeff_nonneg γ]
    · simp [c, hγ, Real.norm_eq_abs,
        abs_of_nonneg (E.gCoeff_nonneg γ)]
  have hc : Summable c := E.summable_gCoeff.of_norm_bounded hc_bound
  have hsum_sdiff :
      (∑ γ ∈ A \ B, E.gCoeff γ) = ∑ γ ∈ A \ B, c γ := by
    refine Finset.sum_congr rfl ?_
    intro γ hγ
    have hnot : γ ∉ B := (Finset.mem_sdiff.mp hγ).2
    simp [c, hnot]
  have hle_tsum :
      (∑ γ ∈ A \ B, c γ) ≤ ∑' γ : E.Group, c γ :=
    hc.sum_le_tsum (A \ B) (fun γ _hγ => hc_nonneg γ)
  have hsumB_c : (∑ γ ∈ B, c γ) = 0 := by
    rw [Finset.sum_eq_zero]
    intro γ hγ
    simp [c, hγ]
  have hcompl_c :
      (∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ) =
        ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
    refine tsum_congr ?_
    intro γ
    have hnot : (γ : E.Group) ∉ B := by
      exact γ.property
    simp [c, hnot]
  have hc_split := hc.sum_add_tsum_compl (s := B)
  have hg_split := E.summable_gCoeff.sum_add_tsum_compl (s := B)
  have htail_c :
      (∑' γ : E.Group, c γ) =
        (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
    calc
      (∑' γ : E.Group, c γ)
          = (∑ γ ∈ B, c γ) +
              ∑' γ : ↑((↑B : Set E.Group)ᶜ), c γ := by
            exact hc_split.symm
      _ = ∑' γ : ↑((↑B : Set E.Group)ᶜ), E.gCoeff γ := by
            rw [hsumB_c, zero_add, hcompl_c]
      _ = (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ := by
            rw [← hg_split]
            ring
  have htail_upper :
      (∑' γ : E.Group, E.gCoeff γ) - ∑ γ ∈ B, E.gCoeff γ ≤ δ := by
    have hle := (abs_le.mp hg_tail).1
    linarith
  rw [hsum_sdiff]
  exact hle_tsum.trans (by simpa [htail_c] using htail_upper)

lemma abs_fejer_nonzero_gCoeff_character_re_le_gCoeff
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group) :
    |(if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re)| ≤ E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using E.gCoeff_nonneg γ
  · have hK_nonneg : 0 ≤ (E.fejerTrigPoly Q γ).re :=
      E.fejerTrigPoly_apply_re_nonneg Q γ
    have hK_le : (E.fejerTrigPoly Q γ).re ≤ 1 :=
      E.fejerTrigPoly_apply_re_le_one Q γ
    have hK_abs_le : |(E.fejerTrigPoly Q γ).re| ≤ 1 := by
      simpa [abs_of_nonneg hK_nonneg] using hK_le
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    calc
      |(if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)|
          = |(E.fejerTrigPoly Q γ).re| * E.gCoeff γ *
              |(E.addCharacterValue z γ).re| := by
                simp [hzero, abs_mul, abs_of_nonneg hK_nonneg,
                  abs_of_nonneg hg_nonneg]
      _ ≤ 1 * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs_le le_rfl hg_nonneg zero_le_one)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg zero_le_one hg_nonneg)
      _ = E.gCoeff γ := by ring

lemma abs_nonzero_gCoeff_character_re_sub_fejer_le
    (E : CayleyExtraction S) (Q : Finset E.Group)
    (z : E.CompactAddDual) (γ : E.Group)
    {M : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ‖1 - E.fejerTrigPoly Q γ‖ ≤ M) :
    |(if γ = 0 then 0
        else E.gCoeff γ * (E.addCharacterValue z γ).re) -
      (if γ = 0 then 0
        else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
          (E.addCharacterValue z γ).re)| ≤ M * E.gCoeff γ := by
  by_cases hzero : γ = 0
  · simpa [hzero] using mul_nonneg hM_nonneg (E.gCoeff_nonneg γ)
  · have hK_abs : |1 - (E.fejerTrigPoly Q γ).re| ≤ M := by
      have hre :
          |(1 - E.fejerTrigPoly Q γ).re| ≤
            ‖1 - E.fejerTrigPoly Q γ‖ :=
        Complex.abs_re_le_norm _
      have hrewrite :
          (1 - E.fejerTrigPoly Q γ).re =
            1 - (E.fejerTrigPoly Q γ).re := by simp
      simpa [hrewrite] using hre.trans hclose
    have hchar_abs : |(E.addCharacterValue z γ).re| ≤ 1 :=
      (Complex.abs_re_le_norm (E.addCharacterValue z γ)).trans
        (by simp [E.norm_addCharacterValue z γ])
    have hg_nonneg : 0 ≤ E.gCoeff γ := E.gCoeff_nonneg γ
    have hdiff :
        (if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
          (if γ = 0 then 0
            else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
              (E.addCharacterValue z γ).re) =
        (1 - (E.fejerTrigPoly Q γ).re) *
          E.gCoeff γ * (E.addCharacterValue z γ).re := by
      simp [hzero, mul_assoc]
      ring
    calc
      |(if γ = 0 then 0 else E.gCoeff γ * (E.addCharacterValue z γ).re) -
        (if γ = 0 then 0
          else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
            (E.addCharacterValue z γ).re)|
          = |(1 - (E.fejerTrigPoly Q γ).re) *
              E.gCoeff γ * (E.addCharacterValue z γ).re| := by
                rw [hdiff]
      _ = |1 - (E.fejerTrigPoly Q γ).re| *
            E.gCoeff γ * |(E.addCharacterValue z γ).re| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hg_nonneg]
      _ ≤ M * E.gCoeff γ * 1 := by
            exact mul_le_mul
              (mul_le_mul hK_abs le_rfl hg_nonneg hM_nonneg)
              hchar_abs
              (abs_nonneg _)
              (mul_nonneg hM_nonneg hg_nonneg)
      _ = M * E.gCoeff γ := by ring

lemma abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
    (E : CayleyExtraction S) (Q : Finset E.Group) (hQ : Q ≠ ∅)
    (z : E.CompactAddDual) (B : Finset E.Group)
    (hB0 : (0 : E.Group) ∈ B)
    {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    (hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ M)
    (hg_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ) :
    |E.compactSmoothReal Q z - E.fReal z| ≤
      2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by
  classical
  let A : Finset E.Group := B ∪ (E.compactSmoothTrigPoly Q).support
  let a : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else E.gCoeff γ * (E.addCharacterValue z γ).re
  let b : E.Group → ℝ :=
    fun γ => if γ = 0 then 0
      else (E.fejerTrigPoly Q γ).re * E.gCoeff γ *
        (E.addCharacterValue z γ).re
  have hBsubA : B ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hA0 : (0 : E.Group) ∈ A := hBsubA hB0
  have hAsupport : (E.compactSmoothTrigPoly Q).support ⊆ A := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inr hγ)
  have hcompact :
      E.compactSmoothReal Q z =
        (E.coeff (0 : E.Group)).re - ∑ γ ∈ A, b γ := by
    simpa [b] using
      E.compactSmoothReal_eq_coeff_zero_sub_sum_nonzero_gCoeff
        Q hQ z A hA0 hAsupport
  have hf :
      E.fReal z =
        (E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ := by
    simpa [a] using E.fReal_eq_coeff_zero_sub_tsum_nonzero_gCoeff z
  have hsplit_b :
      (∑ γ ∈ A, b γ) =
        (∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ := by
    have h := Finset.sum_sdiff (s₁ := B) (s₂ := A) (f := b) hBsubA
    rw [← h]
    ring
  have htail_signed :
      |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| ≤ δ := by
    have h :=
      E.abs_sum_sub_tsum_nonzero_gCoeff_character_re_le_of_gCoeff_tail B z
        hg_tail
    simpa [a, abs_sub_comm] using h
  have hcore :
      |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| ≤
        M * ∑ γ ∈ B, E.gCoeff γ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ γ ∈ B, (a γ - b γ)|
          ≤ ∑ γ ∈ B, |a γ - b γ| := by
            exact Finset.abs_sum_le_sum_abs (fun γ => a γ - b γ) B
      _ ≤ ∑ γ ∈ B, M * E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ hγ
            simpa [a, b] using
              E.abs_nonzero_gCoeff_character_re_sub_fejer_le Q z γ
                hM_nonneg (hclose γ hγ)
      _ = M * ∑ γ ∈ B, E.gCoeff γ := by
            rw [Finset.mul_sum]
  have hextra :
      |∑ γ ∈ A \ B, b γ| ≤ δ := by
    calc
      |∑ γ ∈ A \ B, b γ|
          ≤ ∑ γ ∈ A \ B, |b γ| := by
            exact Finset.abs_sum_le_sum_abs b (A \ B)
      _ ≤ ∑ γ ∈ A \ B, E.gCoeff γ := by
            refine Finset.sum_le_sum ?_
            intro γ _hγ
            simpa [b] using
              E.abs_fejer_nonzero_gCoeff_character_re_le_gCoeff Q z γ
      _ ≤ δ := E.sum_gCoeff_sdiff_le_of_gCoeff_tail B A hg_tail
  rw [hcompact, hf, hsplit_b]
  have hdecomp :
      ((E.coeff (0 : E.Group)).re -
          ((∑ γ ∈ B, b γ) + ∑ γ ∈ A \ B, b γ)) -
        ((E.coeff (0 : E.Group)).re - ∑' γ : E.Group, a γ) =
      ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ := by
    ring
  rw [hdecomp]
  calc
    |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
        ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
          ∑ γ ∈ A \ B, b γ|
        ≤ |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
            |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
              |∑ γ ∈ A \ B, b γ| := by
          calc
            |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ) -
                  ∑ γ ∈ A \ B, b γ|
                = |(((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)) +
                    (-(∑ γ ∈ A \ B, b γ))| := by ring_nf
            _ ≤ |((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ) +
                    ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ)| +
                  |-(∑ γ ∈ A \ B, b γ)| := abs_add_le _ _
            _ ≤ (|(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ|) +
                  |∑ γ ∈ A \ B, b γ| := by
                    simpa [abs_neg] using
                      add_le_add_right
                        (abs_add_le
                          ((∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ)
                          ((∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ))
                        |∑ γ ∈ A \ B, b γ|
            _ = |(∑' γ : E.Group, a γ) - ∑ γ ∈ B, a γ| +
                    |(∑ γ ∈ B, a γ) - ∑ γ ∈ B, b γ| +
                  |∑ γ ∈ A \ B, b γ| := by ring
    _ ≤ δ + M * ∑ γ ∈ B, E.gCoeff γ + δ := by
          exact add_le_add (add_le_add htail_signed hcore) hextra
    _ = 2 * δ + M * ∑ γ ∈ B, E.gCoeff γ := by ring

theorem exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (Bextra : Finset E.Group)
    {ε Mlarge : ℝ} (hε : 0 < ε) (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      ∀ z : E.CompactAddDual,
        |E.compactSmoothReal Q z - E.fReal z| ≤ ε := by
  classical
  let δ : ℝ := ε / 4
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have htail_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp E.summable_gCoeff.hasSum δ hδ_pos)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp htail_event
  let Bcore : Finset E.Group := insert 0 B₀
  let B : Finset E.Group := Bcore ∪ Bextra
  have hB_ge : B ≥ B₀ := by
    intro γ hγ
    exact Finset.mem_union_left Bextra (Finset.mem_insert.mpr (Or.inr hγ))
  have hB_tail_lt : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ :=
    hB₀ B hB_ge
  have hB_tail :
      |(∑ γ ∈ B, E.gCoeff γ) - ∑' γ : E.Group, E.gCoeff γ| ≤ δ := by
    simpa [Gtot] using le_of_lt hB_tail_lt
  have hB0 : (0 : E.Group) ∈ B := by
    exact Finset.mem_union_left Bextra (Finset.mem_insert_self _ _)
  let SB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hSB_nonneg : 0 ≤ SB := by
    dsimp [SB]
    exact Finset.sum_nonneg fun γ _hγ => E.gCoeff_nonneg γ
  let Mapprox : ℝ := δ / (SB + 1)
  have hden_pos : 0 < SB + 1 := by
    nlinarith
  have hMapprox_pos : 0 < Mapprox := by
    dsimp [Mapprox]
    exact div_pos hδ_pos hden_pos
  let Mchoose : ℝ := min Mapprox Mlarge
  have hMchoose_pos : 0 < Mchoose := by
    dsimp [Mchoose]
    exact lt_min hMapprox_pos hMlarge
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hMchoose_pos
  have hchoose_le_approx : Mchoose ≤ Mapprox := by
    dsimp [Mchoose]
    exact min_le_left _ _
  have hchoose_le_large : Mchoose ≤ Mlarge := by
    dsimp [Mchoose]
    exact min_le_right _ _
  have hclose_choose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mchoose :=
    E.fejerCoeffBound_of_pairCoeffLowerBound hQ hlower
  have hclose : ∀ γ ∈ B, ‖1 - E.fejerTrigPoly Q γ‖ ≤ Mapprox := by
    intro γ hγ
    exact (hclose_choose γ hγ).trans hchoose_le_approx
  have hBextra :
      E.FejerPairCoeffLowerBound Q Bextra Mlarge := by
    intro γ hγ
    have hγB : γ ∈ B := Finset.mem_union_right Bcore hγ
    have hlow := hlower γ hγB
    have hle : 1 - Mlarge ≤ 1 - Mchoose := by linarith
    exact hle.trans hlow
  refine ⟨Q, hQ, hBextra, ?_⟩
  intro z
  have hmain :=
    E.abs_compactSmoothReal_sub_fReal_le_of_core_fejer_and_gCoeff_tail
      Q hQ z B hB0 (le_of_lt hMapprox_pos) hclose hB_tail
  have hM_mul : Mapprox * SB ≤ δ := by
    dsimp [Mapprox]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    nlinarith
  calc
    |E.compactSmoothReal Q z - E.fReal z|
        ≤ 2 * δ + Mapprox * ∑ γ ∈ B, E.gCoeff γ := hmain
    _ = 2 * δ + Mapprox * SB := by rfl
    _ ≤ 2 * δ + δ := by
          nlinarith
    _ ≤ ε := by
          dsimp [δ]
          nlinarith

lemma gReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.gReal z := by
  intro z
  rw [E.gReal_eq_tsum_gCoeff_mul_character_re E.summable_gCoeff z]
  let a : E.Group → ℝ :=
    fun γ => E.gCoeff γ * (E.addCharacterValue z γ).re
  let T : ℝ := ∑' γ : E.Group, a γ
  change 0 ≤ T
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by positivity
  have hsumA : Summable a := by
    simpa [a] using E.summable_gCoeff_mul_character_re E.summable_gCoeff z
  have hsumG : Summable E.gCoeff := E.summable_gCoeff
  let Gtot : ℝ := ∑' γ : E.Group, E.gCoeff γ
  have hA_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, a γ) - T| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumA.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, T] using hB
  have hG_event :
      ∀ᶠ B : Finset E.Group in atTop,
        |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := by
    have h := (Metric.tendsto_nhds.mp hsumG.hasSum δ hδ)
    filter_upwards [h] with B hB
    simpa [Real.dist_eq, Gtot] using hB
  obtain ⟨B, hB⟩ :=
    (Filter.eventually_atTop.mp (hA_event.and hG_event))
  have hB_self := hB B (le_rfl : B ≥ B)
  have hA_B : |(∑ γ ∈ B, a γ) - T| < δ := hB_self.1
  have hG_B : |(∑ γ ∈ B, E.gCoeff γ) - Gtot| < δ := hB_self.2
  let GB : ℝ := ∑ γ ∈ B, E.gCoeff γ
  have hGB_nonneg : 0 ≤ GB := by
    dsimp [GB]
    exact Finset.sum_nonneg (fun γ _hγ => E.gCoeff_nonneg γ)
  let M : ℝ := δ / ((GB + 1) * (δ + 1))
  have hden_pos : 0 < (GB + 1) * (δ + 1) := by positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    exact div_pos hδ hden_pos
  have hM_lt : M < 1 := by
    dsimp [M]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hGB_nonneg, hδ]
  have hMGB_le : M * GB ≤ δ := by
    dsimp [M]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden_pos]
    have hden_ge : GB ≤ (GB + 1) * (δ + 1) := by
      nlinarith [hGB_nonneg, hδ]
    exact mul_le_mul_of_nonneg_left hden_ge (le_of_lt hδ)
  obtain ⟨Q, hQ, hlower⟩ := E.exists_fejerPairCoeffLowerBound B hM_pos
  let P : E.TrigPoly := E.shiftedFejerTrigPoly Q z
  let C : Finset E.Group := P.support \ B
  let D : Finset E.Group := B ∪ C
  have hD_ge : D ≥ B := by
    intro γ hγ
    exact Finset.mem_union.mpr (Or.inl hγ)
  have hD_close := hB D hD_ge
  have hG_D : |(∑ γ ∈ D, E.gCoeff γ) - Gtot| < δ := hD_close.2
  have hdisj : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro γ hγB hγC
    exact (Finset.mem_sdiff.mp hγC).2 hγB
  have hsumD :
      (∑ γ ∈ D, E.gCoeff γ) =
        (∑ γ ∈ B, E.gCoeff γ) + ∑ γ ∈ C, E.gCoeff γ := by
    dsimp [D]
    rw [Finset.sum_union hdisj]
  have hC_lt : (∑ γ ∈ C, E.gCoeff γ) < 2 * δ := by
    have hD_upper : (∑ γ ∈ D, E.gCoeff γ) - Gtot < δ :=
      (abs_sub_lt_iff.mp hG_D).1
    have hB_lower : Gtot - (∑ γ ∈ B, E.gCoeff γ) < δ :=
      (abs_sub_lt_iff.mp hG_B).2
    linarith
  have hfinite :=
    E.sum_gCoeff_mul_character_re_ge_neg_of_fejerPairCoeffLowerBound
      Q B z hQ hM_lt hlower
  have hsumB_lower : -(3 * δ) < ∑ γ ∈ B, a γ := by
    dsimp [C, P, a, GB] at hfinite hC_lt hMGB_le
    nlinarith
  have hT_lower : -(4 * δ) < T := by
    have hA_lower : (∑ γ ∈ B, a γ) - T < δ :=
      (abs_sub_lt_iff.mp hA_B).1
    nlinarith
  have hδ_eq : 4 * δ = ε := by
    dsimp [δ]
    ring
  linarith

lemma norm_gComplex_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    ‖E.gComplex z‖ ≤ ∑' γ : E.Group, E.gCoeff γ := by
  have hnorm_summable :
      Summable fun γ : E.Group => ‖E.gComplexTerm γ z‖ := by
    simpa [E.norm_gComplexTerm_eq_gCoeff] using hsum
  unfold gComplex
  calc
    ‖∑' γ : E.Group, E.gComplexTerm γ z‖
        ≤ ∑' γ : E.Group, ‖E.gComplexTerm γ z‖ :=
      norm_tsum_le_tsum_norm hnorm_summable
    _ = ∑' γ : E.Group, E.gCoeff γ := by
      exact tsum_congr fun γ => E.norm_gComplexTerm_eq_gCoeff γ z

lemma gReal_le_tsum_gCoeff
    (E : CayleyExtraction S) (hsum : Summable E.gCoeff)
    (z : E.CompactAddDual) :
    E.gReal z ≤ ∑' γ : E.Group, E.gCoeff γ := by
  unfold gReal
  exact (Complex.re_le_norm (E.gComplex z)).trans
    (E.norm_gComplex_le_tsum_gCoeff hsum z)

lemma gReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.gReal z ≤ 1 := by
  intro z
  exact (E.gReal_le_tsum_gCoeff E.summable_gCoeff z).trans
    E.tsum_gCoeff_le_one

lemma fReal_nonneg (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, 0 ≤ E.fReal z := by
  intro z
  unfold fReal
  linarith [E.gReal_le_one z]

lemma fReal_le_one (E : CayleyExtraction S) :
    ∀ z : E.CompactAddDual, E.fReal z ≤ 1 := by
  intro z
  unfold fReal
  linarith [E.gReal_nonneg z]

lemma levelOne_character_eq_one_of_gReal_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (htsum : (∑' γ : E.Group, E.gCoeff γ) = 1)
    {x : E.CompactAddDual} (hx : E.gReal x = 1)
    {γ : E.Group} (hγ : 0 < E.gCoeff γ) :
    E.addCharacterValue x γ = 1 := by
  classical
  have hre_le : ∀ δ : E.Group, (E.addCharacterValue x δ).re ≤ 1 :=
    fun δ => E.addCharacterValue_re_le_one x δ
  have hmul_summable := E.summable_gCoeff_mul_character_re hsum x
  have hdef_nonneg :
      ∀ δ : E.Group,
        0 ≤ E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re := by
    intro δ
    have hcoeff_nonneg : 0 ≤ E.gCoeff δ := E.gCoeff_nonneg δ
    have hfactor_nonneg : 0 ≤ 1 - (E.addCharacterValue x δ).re := by
      linarith [hre_le δ]
    nlinarith [mul_nonneg hcoeff_nonneg hfactor_nonneg]
  let dNN : E.Group → NNReal := fun δ =>
    ⟨E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re,
      hdef_nonneg δ⟩
  have hdef_summable :
      Summable fun δ : E.Group =>
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re) := by
    exact hsum.sub hmul_summable
  have hdNN_summable : Summable dNN := by
    rw [← NNReal.summable_coe]
    change Summable fun δ : E.Group =>
      E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re
    exact hdef_summable
  have hdef_tsum_zero :
      (∑' δ : E.Group,
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) = 0 := by
    have hsub :=
      hsum.hasSum.sub hmul_summable.hasSum
    have hsub_tsum :
        (∑' δ : E.Group,
          (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) =
          (∑' δ : E.Group, E.gCoeff δ) -
            (∑' δ : E.Group,
              E.gCoeff δ * (E.addCharacterValue x δ).re) := by
      exact hsub.tsum_eq
    rw [hsub_tsum]
    rw [htsum, ← E.gReal_eq_tsum_gCoeff_mul_character_re hsum x, hx]
    ring
  have hdNN_tsum_zero : (∑' δ : E.Group, dNN δ) = 0 := by
    apply NNReal.eq
    rw [NNReal.coe_tsum]
    change
      (∑' δ : E.Group,
        (E.gCoeff δ - E.gCoeff δ * (E.addCharacterValue x δ).re)) = 0
    exact hdef_tsum_zero
  by_contra hne
  have hre_lt : (E.addCharacterValue x γ).re < 1 := by
    have hle := hre_le γ
    by_contra hnot
    have hre_eq : (E.addCharacterValue x γ).re = 1 := le_antisymm hle (not_lt.mp hnot)
    exact hne (E.addCharacterValue_eq_one_of_re_eq_one x γ hre_eq)
  have hdNN_pos : 0 < dNN γ := by
    change 0 < E.gCoeff γ - E.gCoeff γ * (E.addCharacterValue x γ).re
    nlinarith [mul_lt_mul_of_pos_left hre_lt hγ]
  have htsum_pos : 0 < ∑' δ : E.Group, dNN δ :=
    NNReal.tsum_pos hdNN_summable γ hdNN_pos
  exact (ne_of_gt htsum_pos) hdNN_tsum_zero

/-- Conditional level-one subgroup closure for the compact complement kernel.

The remaining positive-definite equality case has to prove `hchars`: if
`gReal x = 1`, then every character with positive coefficient is trivial at
`x`.  Once that is known, closure under subtraction is just character algebra
and termwise equality of the Fourier series. -/
lemma levelOneSubgroupKernel_gReal_of_levelOne_chars
    (E : CayleyExtraction S)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1)
    (hchars :
      ∀ x : E.CompactAddDual, E.gReal x = 1 →
        ∀ γ : E.Group, 0 < E.gCoeff γ →
          E.addCharacterValue x γ = 1) :
    LevelOneSubgroupKernel E.gReal where
  map_zero := hg0
  sub_mem := by
    intro x y hx hy
    have hcomplex :
        E.gComplex (x - y) = E.gComplex (0 : E.CompactAddDual) := by
      unfold gComplex
      refine tsum_congr ?_
      intro γ
      by_cases hpos : 0 < E.gCoeff γ
      · have hxγ : E.addCharacterValue x γ = 1 := hchars x hx γ hpos
        have hyγ : E.addCharacterValue y γ = 1 := hchars y hy γ hpos
        have hxyγ : E.addCharacterValue (x - y) γ = 1 := by
          rw [sub_eq_add_neg, E.addCharacterValue_add_point,
            E.addCharacterValue_neg_point, hxγ, hyγ]
          simp
        unfold gComplexTerm
        simp [hxyγ]
      · have hzero : E.gCoeff γ = 0 :=
          le_antisymm (not_lt.mp hpos) (E.gCoeff_nonneg γ)
        simp [gComplexTerm, hzero]
    change (E.gComplex (x - y)).re = 1
    rw [hcomplex]
    simpa [gReal] using hg0

lemma levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    LevelOneSubgroupKernel E.gReal := by
  have htsum : (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  exact E.levelOneSubgroupKernel_gReal_of_levelOne_chars hg0
    (fun x hx γ hpos =>
      E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum hx hpos)

lemma exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one
    (E : CayleyExtraction S) (hη : 0 < η)
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ∃ γ : E.Group, γ ≠ 0 ∧ 0 < E.gCoeff γ := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero_nonzero : ∀ γ : E.Group, γ ≠ 0 → E.gCoeff γ = 0 := by
    intro γ hγ
    exact le_antisymm (hnone γ hγ) (E.gCoeff_nonneg γ)
  have htsum_single :
      (∑' γ : E.Group, E.gCoeff γ) = E.gCoeff 0 := by
    exact tsum_eq_single (0 : E.Group) (by
      intro γ hγ
      exact hzero_nonzero γ hγ)
  have htsum_one :
      (∑' γ : E.Group, E.gCoeff γ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hcoeff_zero_one : E.gCoeff 0 = 1 := by
    rw [← htsum_single, htsum_one]
  have hle := E.gCoeff_zero_le_one_sub_eta
  nlinarith

lemma levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
    (E : CayleyExtraction S)
    (hsum : Summable E.gCoeff) (hη : 0 < η)
    {hg_level : LevelOneSubgroupKernel E.gReal}
    (hg0 : E.gReal (0 : E.CompactAddDual) = 1) :
    ¬ (levelOneAddSubgroup E.gReal hg_level :
      AddSubgroup E.CompactAddDual).FiniteIndex := by
  classical
  intro hfinite
  let H : AddSubgroup E.CompactAddDual :=
    levelOneAddSubgroup E.gReal hg_level
  obtain ⟨γ, hγ_ne, hγ_pos⟩ :=
    E.exists_ne_zero_gCoeff_pos_of_gReal_zero_eq_one hη hg0
  have htsum :
      (∑' δ : E.Group, E.gCoeff δ) = 1 := by
    rw [← E.gReal_zero_eq_tsum_gCoeff]
    exact hg0
  have hchar_on_H :
      ∀ x : E.CompactAddDual, x ∈ H → E.addCharacterValue x γ = 1 := by
    intro x hx
    exact E.levelOne_character_eq_one_of_gReal_eq_one hsum htsum
      (mem_levelOneAddSubgroup.mp hx) hγ_pos
  let N : ℕ := Nat.factorial H.index
  have hN_pos : 0 < N := Nat.factorial_pos H.index
  have hN_mem_H : ∀ x : E.CompactAddDual, N • x ∈ H := by
    intro x
    exact AddSubgroup.nsmul_mem_of_index_ne_zero_of_dvd
      (H := H) hfinite.index_ne_zero x
      (n := N) (fun m hm_pos hm_le => Nat.dvd_factorial hm_pos hm_le)
  have hchar_nsmul_all :
      ∀ x : E.CompactAddDual, E.addCharacterValue x (N • γ) = 1 := by
    intro x
    have hxchar : E.addCharacterValue (N • x) γ = 1 :=
      hchar_on_H (N • x) (hN_mem_H x)
    rw [E.addCharacterValue_nsmul_point] at hxchar
    rw [E.addCharacterValue_nsmul_frequency]
    exact hxchar
  have hNγ_zero : N • γ = 0 := by
    by_contra hNγ_ne
    rcases E.exists_dual_point_ne_one hNγ_ne with ⟨x, hx⟩
    exact hx (hchar_nsmul_all x)
  have hγ_zero : γ = 0 := by
    have hinj := nsmul_right_injective (M := E.Group) (Nat.ne_of_gt hN_pos)
    exact hinj (by simpa using hNγ_zero)
  exact hγ_ne hγ_zero

/-- Compact positive clique-density endpoint with connectedness replaced by the
finite-index contradiction proved from extraction torsion-freeness and the mean
gap.  The remaining analytic input is the pointwise bound `0 ≤ gReal ≤ 1` and
summability of `gCoeff`. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    (E : CayleyExtraction S)
    (_hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hsum : Summable E.gCoeff)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x)
    (hg_le : ∀ x : E.CompactAddDual, E.gReal x ≤ 1) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal := by
  classical
  let : CompactSpace E.CompactAddDual := E.compactAddDual_compactSpace
  let : T2Space E.CompactAddDual := E.compactAddDual_t2Space
  let : IsTopologicalAddGroup E.CompactAddDual :=
    E.compactAddDual_isTopologicalAddGroup
  have hbranch :
      E.gReal (0 : E.CompactAddDual) < 1 ∨
        ∃ hg_level : LevelOneSubgroupKernel E.gReal,
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex := by
    by_cases hlt : E.gReal (0 : E.CompactAddDual) < 1
    · exact Or.inl hlt
    · have hg0 : E.gReal (0 : E.CompactAddDual) = 1 :=
        le_antisymm (hg_le 0) (not_lt.mp hlt)
      let hg_level : LevelOneSubgroupKernel E.gReal :=
        E.levelOneSubgroupKernel_gReal_of_gReal_zero_eq_one hsum hg0
      have hnot :
          ¬ (levelOneAddSubgroup E.gReal hg_level :
            AddSubgroup E.CompactAddDual).FiniteIndex :=
        E.levelOneAddSubgroup_gReal_not_finiteIndex_of_gReal_zero_eq_one
          hsum hη hg0
      exact Or.inr ⟨hg_level, hnot⟩
  change
    0 < continuousCliqueDensity E.haar ℓ
      (fun x : E.CompactAddDual => 1 - E.gReal x)
  exact
    continuousCliqueDensity_pos_of_lt_one_or_levelOneSubgroupKernel_not_finiteIndex
      E.haar ℓ E.gReal (E.gReal_continuous hsum)
      hg_nonneg hg_le hbranch

/-- Compact positive clique-density endpoint with summability and the upper
pointwise bound already discharged. -/
theorem compact_limit_cliqueDensity_pos_of_gReal_nonneg
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (hg_nonneg : ∀ x : E.CompactAddDual, 0 ≤ E.gReal x) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_bounds_infiniteIndex
    hℓ hη E.summable_gCoeff hg_nonneg E.gReal_le_one

/-- Compact positive clique-density endpoint for the compact-Cayley extraction
kernel, with all pointwise bounds discharged. -/
theorem compact_limit_cliqueDensity_pos
    (E : CayleyExtraction S)
    (hℓ : 2 ≤ ℓ) (hη : 0 < η) :
    0 < continuousCliqueDensity E.haar ℓ E.fReal :=
  E.compact_limit_cliqueDensity_pos_of_gReal_nonneg hℓ hη E.gReal_nonneg

theorem compactSmoothReal_cliqueDensity_ge_sub_error_of_close
    (E : CayleyExtraction S) (Q : Finset E.Group) {κ : ℝ}
    (hκ_nonneg : 0 ≤ κ) (hκ_le_one : κ ≤ 1)
    (hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ) :
    continuousCliqueDensity E.haar ℓ E.fReal -
        ((((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
          (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card) ≤
      continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let C : ℝ := (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
    (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  have hf_abs : ∀ z : E.CompactAddDual, |E.fReal z| ≤ 2 := by
    intro z
    have hnonneg := E.fReal_nonneg z
    have hle := E.fReal_le_one z
    rw [abs_of_nonneg hnonneg]
    linarith
  have hs_abs : ∀ z : E.CompactAddDual, |E.compactSmoothReal Q z| ≤ 2 := by
    intro z
    have hf_abs_one : |E.fReal z| ≤ 1 := by
      have hnonneg := E.fReal_nonneg z
      have hle := E.fReal_le_one z
      rw [abs_of_nonneg hnonneg]
      exact hle
    have hclose' : |E.compactSmoothReal Q z - E.fReal z| ≤ κ := by
      simpa [abs_sub_comm] using hclose z
    calc
      |E.compactSmoothReal Q z|
          = |(E.compactSmoothReal Q z - E.fReal z) + E.fReal z| := by ring_nf
      _ ≤ |E.compactSmoothReal Q z - E.fReal z| + |E.fReal z| := abs_add_le _ _
      _ ≤ κ + 1 := add_le_add hclose' hf_abs_one
      _ ≤ 2 := by linarith
  have hdiff :=
    continuousCliqueDensity_lipschitz_sup_two_pow
      E.haar ℓ
      (E.fReal_continuous E.summable_gCoeff).measurable
      (E.compactSmoothReal_continuous Q).measurable
      hf_abs hs_abs hκ_nonneg hclose
  have hlow :
      continuousCliqueDensity E.haar ℓ E.fReal -
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ≤ C := by
    exact (le_abs_self _).trans (by simpa [C] using hdiff)
  have htarget :
      continuousCliqueDensity E.haar ℓ E.fReal - C ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    linarith
  simpa [C] using htarget

theorem exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
    (E : CayleyExtraction S) (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (Bextra : Finset E.Group) {Mlarge : ℝ} (hMlarge : 0 < Mlarge) :
    ∃ Q : Finset E.Group, Q ≠ ∅ ∧
      E.FejerPairCoeffLowerBound Q Bextra Mlarge ∧
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) ∧
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
  classical
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let edgeCount : ℝ := ((continuousCliqueEdgePairs ℓ).card : ℝ)
  let P : ℝ := (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card
  let A : ℝ := (edgeCount + 1) * (P + 1)
  have hedge_nonneg : 0 ≤ edgeCount := by
    dsimp [edgeCount]
    exact Nat.cast_nonneg _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hA_pos : 0 < A := by
    dsimp [A]
    nlinarith
  let κ : ℝ := min 1 (ρ / (2 * A))
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact lt_min zero_lt_one (div_pos hρ_pos (mul_pos two_pos hA_pos))
  have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
  have hκ_le_one : κ ≤ 1 := by
    dsimp [κ]
    exact min_le_left _ _
  obtain ⟨Q, hQ, hBextra, hclose₀⟩ :=
    E.exists_compactSmoothReal_uniform_close_and_fejerPairCoeffLowerBound
      Bextra hκ_pos hMlarge
  have hclose : ∀ z : E.CompactAddDual,
      |E.fReal z - E.compactSmoothReal Q z| ≤ κ := by
    intro z
    simpa [abs_sub_comm] using hclose₀ z
  have hκA_le : κ * A ≤ ρ / 2 := by
    have hκ_le : κ ≤ ρ / (2 * A) := by
      dsimp [κ]
      exact min_le_right _ _
    calc
      κ * A ≤ (ρ / (2 * A)) * A :=
        mul_le_mul_of_nonneg_right hκ_le (le_of_lt hA_pos)
      _ = ρ / 2 := by
        field_simp [ne_of_gt hA_pos]
  have hedgeP_le_A : edgeCount * P ≤ A := by
    dsimp [A]
    nlinarith
  have hmargin :
      (edgeCount * κ) * P < ρ := by
    have hC_le : (edgeCount * κ) * P ≤ κ * A := by
      have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
      nlinarith
    nlinarith
  have hge :
      continuousCliqueDensity E.haar ℓ E.fReal / 2 ≤
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hlower :=
      E.compactSmoothReal_cliqueDensity_ge_sub_error_of_close Q
        hκ_nonneg hκ_le_one hclose
    have hC_le :
        (((continuousCliqueEdgePairs ℓ).card : ℝ) * κ) *
            (2 : ℝ) ^ (continuousCliqueEdgePairs ℓ).card ≤
          ρ / 2 := by
      have hC_le_A : (edgeCount * κ) * P ≤ κ * A := by
        have h := mul_le_mul_of_nonneg_left hedgeP_le_A hκ_nonneg
        nlinarith
      simpa [edgeCount, P] using hC_le_A.trans hκA_le
    dsimp [ρ] at hC_le
    linarith
  have hpos :
      0 < continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) :=
    lt_of_lt_of_le (half_pos hρ_pos) (by simpa [ρ] using hge)
  refine ⟨Q, hQ, hBextra, hpos, hge⟩

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/SmoothDensityConvergence.lean
    ============================================================= -/

/-
Erdős Problem 42 — finite-to-compact density convergence for smoothed kernels.

This file contains the finite edge-frequency bookkeeping needed to turn the
fixed-`Q` finite Fejér-smoothed clique density into a compact Haar integral.
-/

namespace Erdos42.CompactCayley

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace CayleyExtraction

variable {ℓ : ℕ} {η : ℝ} {S : CayleyCounterSeq ℓ η}

/-- The finite type of oriented clique edges. -/
abbrev CliqueEdgeIndex (M : ℕ) : Type :=
  {e : Fin M × Fin M // e ∈ cliqueEdgePairs M}

/-- Extend an assignment on clique edges by zero off the clique-edge set. -/
noncomputable def extendCliqueEdgeAssignment
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Fin M × Fin M → E.Group :=
  fun e => if h : e ∈ cliqueEdgePairs M then ω ⟨e, h⟩ else 0

@[simp]
lemma extendCliqueEdgeAssignment_apply_mem
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (e : Fin M × Fin M)
    (he : e ∈ cliqueEdgePairs M) :
    E.extendCliqueEdgeAssignment ω e = ω ⟨e, he⟩ := by
  simp [extendCliqueEdgeAssignment, he]

/-- Coefficient product attached to an assignment of frequencies to the clique
edges. -/
noncomputable def cliqueEdgeAssignmentCoeff
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) : ℂ :=
  ∏ e : CliqueEdgeIndex M, P (ω e)

lemma TrigPoly.evalFinite_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly) (n : ℕ)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    TrigPoly.evalFinite P n x =
      ∑ γ ∈ A, P γ * ZMod.stdAddChar (-(E.lift n γ * x)) := by
  classical
  unfold TrigPoly.evalFinite
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma TrigPoly.evalAdd_eq_sum_of_support_subset
    (E : CayleyExtraction S) (P : E.TrigPoly)
    (A : Finset E.Group) (hP : P.support ⊆ A)
    (z : E.CompactAddDual) :
    TrigPoly.evalAdd P z =
      ∑ γ ∈ A, P γ * E.addCharacterValue z γ := by
  classical
  unfold TrigPoly.evalAdd
  rw [Finsupp.sum_of_support_subset (f := P) (s := A) hP]
  intro γ _hγ
  simp

lemma addCharacterValue_sum
    (E : CayleyExtraction S) {ι : Type*} (s : Finset ι)
    (z : E.CompactAddDual) (f : ι → E.Group) :
    E.addCharacterValue z (∑ i ∈ s, f i) =
      ∏ i ∈ s, E.addCharacterValue z (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [E.addCharacterValue_add, ih]

lemma stdAddChar_sum
    {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι)
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) =
      ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    rw [ZMod.stdAddChar.map_add_eq_mul, ih]

lemma stdAddChar_sum_univ
    {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι]
    (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i, f i) =
      ∏ i, ZMod.stdAddChar (f i) := by
  simpa using stdAddChar_sum (Finset.univ : Finset ι) f

lemma finitePiAverage_prod_zmod {p M : ℕ} [NeZero p]
    (φ : Fin M → ZMod p → ℂ) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p, ∏ i : Fin M, φ i (x i) =
      ∏ i : Fin M, avgZMod (φ i) := by
  classical
  have hcard_nat : Fintype.card (Fin M → ZMod p) = p ^ M := by
    simp [ZMod.card]
  have hcard_complex : (Fintype.card (Fin M → ZMod p) : ℂ) = (p : ℂ) ^ M := by
    rw [hcard_nat]
    norm_cast
  unfold avgZMod
  rw [hcard_complex]
  rw [Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  rw [Fintype.piFinset_univ]
  simp

lemma finitePiAverage_prod_stdAddChar_neg_mul
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod p,
            ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
        ∏ i : Fin M,
          avgZMod (fun x : ZMod p => ZMod.stdAddChar (-(β i * x))) by
        simpa using
          finitePiAverage_prod_zmod
            (p := p) (M := M)
            (fun i x => ZMod.stdAddChar (-(β i * x)))]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact avgZMod_stdAddChar_neg_mul_eq_ite (β i)

lemma finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    {p M : ℕ} [Fact p.Prime] [NeZero p]
    (β : Fin M → ZMod p) :
    ((Fintype.card (Fin M → ZMod p) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod p,
          ∏ i : Fin M, ZMod.stdAddChar (-(β i * x i)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [finitePiAverage_prod_stdAddChar_neg_mul β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push Not at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Net finite frequency at a vertex for an arbitrary finite set of oriented
edges. The compact-Cayley clique balance is this construction specialized to
`cliqueEdgePairs`. -/
noncomputable def finiteEdgeFrequencyBalanceOn
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (i : Fin M) : ZMod p :=
  (∑ e ∈ s.filter (fun e => e.1 = i), r e) -
  (∑ e ∈ s.filter (fun e => e.2 = i), r e)

lemma sum_vertex_outgoing_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.1 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.1 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.1 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.1 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma sum_vertex_incoming_eq_edge_sum
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) =
      ∑ e ∈ s, r e * x e.2 := by
  classical
  calc
    (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i)
        = ∑ i : Fin M, ∑ e ∈ s, (if e.2 = i then r e else 0) * x i := by
          simp [Finset.sum_mul]
    _ = ∑ e ∈ s, ∑ i : Fin M, (if e.2 = i then r e else 0) * x i := by
          rw [Finset.sum_comm]
    _ = ∑ e ∈ s, r e * x e.2 := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          rw [Finset.sum_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma finiteEdgeFrequencyBalanceOn_exponent_identity
    {p M : ℕ} (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∑ e ∈ s, -(r e * (x e.1 - x e.2))) =
      ∑ i : Fin M, -(finiteEdgeFrequencyBalanceOn s r i * x i) := by
  classical
  simp only [Finset.sum_neg_distrib, neg_inj]
  unfold finiteEdgeFrequencyBalanceOn
  simp only [Finset.sum_filter]
  rw [show
      (∑ i : Fin M,
        ((∑ e ∈ s, if e.1 = i then r e else 0) -
          (∑ e ∈ s, if e.2 = i then r e else 0)) * x i) =
        (∑ i : Fin M, (∑ e ∈ s, if e.1 = i then r e else 0) * x i) -
          (∑ i : Fin M, (∑ e ∈ s, if e.2 = i then r e else 0) * x i) by
        simp [sub_mul, Finset.sum_sub_distrib]]
  rw [sum_vertex_outgoing_eq_edge_sum s r x,
    sum_vertex_incoming_eq_edge_sum s r x]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _he
  ring

lemma prod_stdAddChar_edge_eq_prod_balance
    {p M : ℕ} [NeZero p] (s : Finset (Fin M × Fin M))
    (r : Fin M × Fin M → ZMod p) (x : Fin M → ZMod p) :
    (∏ e ∈ s, ZMod.stdAddChar (-(r e * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(finiteEdgeFrequencyBalanceOn s r i * x i)) := by
  rw [← stdAddChar_sum s (fun e => -(r e * (x e.1 - x e.2)))]
  rw [← stdAddChar_sum_univ
    (fun i : Fin M => -(finiteEdgeFrequencyBalanceOn s r i * x i))]
  rw [finiteEdgeFrequencyBalanceOn_exponent_identity]

lemma prod_vertex_outgoing_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1) =
      ∏ e ∈ s, F e e.1 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.1 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.1 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.1 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.1]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma prod_vertex_incoming_eq_edge_prod
    {M : ℕ} {A : Type*} [CommMonoid A]
    (s : Finset (Fin M × Fin M)) (F : (Fin M × Fin M) → Fin M → A) :
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1) =
      ∏ e ∈ s, F e e.2 := by
  classical
  calc
    (∏ i : Fin M, ∏ e ∈ s, if e.2 = i then F e i else 1)
        = ∏ e ∈ s, ∏ i : Fin M, if e.2 = i then F e i else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ e ∈ s, F e e.2 := by
          refine Finset.prod_congr rfl ?_
          intro e _he
          rw [Finset.prod_eq_single e.2]
          · simp
          · intro i _hi hne
            simp [Ne.symm hne]
          · intro hnot
            exact (hnot (by simp)).elim

lemma compactPiIntegral_prod_addCharacterValue
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
  calc
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∏ i : Fin M, ∫ z : E.CompactAddDual, E.addCharacterValue z (β i) ∂E.haar := by
        simpa using
          (MeasureTheory.integral_fintype_prod_eq_prod
            (μ := fun _ : Fin M => E.haar)
            (f := fun i (z : E.CompactAddDual) => E.addCharacterValue z (β i)))
    _ = ∏ i : Fin M, if β i = 0 then (1 : ℂ) else 0 := by
      refine Finset.prod_congr rfl ?_
      intro i _hi
      exact E.integral_addCharacterValue (β i)

lemma compactPiIntegral_prod_addCharacterValue_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (β : Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        ∏ i : Fin M, E.addCharacterValue (x i) (β i)
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, β i = 0) then 1 else 0 := by
  rw [E.compactPiIntegral_prod_addCharacterValue β]
  by_cases hβ : ∀ i : Fin M, β i = 0
  · simp [hβ]
  · rw [if_neg hβ]
    push Not at hβ
    rcases hβ with ⟨i, hi⟩
    exact Finset.prod_eq_zero (by simp : i ∈ (Finset.univ : Finset (Fin M)))
      (by simp [hi])

/-- Sum of edge frequencies leaving a vertex in the oriented clique edge set. -/
noncomputable def cliqueOutgoingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e

/-- Sum of edge frequencies entering a vertex in the oriented clique edge set. -/
noncomputable def cliqueIncomingFreq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e

/-- Net compact frequency at a vertex after multiplying edge characters
`χ_γ(x_i - x_j)` over all oriented clique edges `i < j`. -/
noncomputable def cliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) : E.Group :=
  E.cliqueOutgoingFreq ω i - E.cliqueIncomingFreq ω i

/-- Finite cyclic lift of the vertex frequency balance attached to an
edge-frequency assignment. -/
noncomputable def finiteCliqueFrequencyBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    ZMod (S.p (E.φ n)) :=
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
    E.lift n (ω e)) -
  (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
    E.lift n (ω e))

lemma finiteLift_cliqueOutgoingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueOutgoingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i),
          E.lift n (ω e) := by
  let s : Finset (Fin M × Fin M) :=
    (cliqueEdgePairs M).filter (fun e => e.1 = i)
  change
    ∀ᶠ n in atTop,
      E.data.finiteLift n (∑ e ∈ s, ω e) =
        ∑ e ∈ s, E.data.finiteLift n (ω e)
  exact E.data.finiteLift_sum_eventually_eq s ω

lemma finiteLift_cliqueIncomingFreq_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueIncomingFreq ω i) =
        ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i),
          E.lift n (ω e) := by
  let s : Finset (Fin M × Fin M) :=
    (cliqueEdgePairs M).filter (fun e => e.2 = i)
  change
    ∀ᶠ n in atTop,
      E.data.finiteLift n (∑ e ∈ s, ω e) =
        ∑ e ∈ s, E.data.finiteLift n (ω e)
  exact E.data.finiteLift_sum_eventually_eq s ω

lemma finiteLift_cliqueFrequencyBalance_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (i : Fin M) :
    ∀ᶠ n in atTop,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  filter_upwards
    [E.data.finiteLift_sub_eventually_eq
      (E.cliqueOutgoingFreq ω i) (E.cliqueIncomingFreq ω i),
      E.finiteLift_cliqueOutgoingFreq_eventually_eq ω i,
      E.finiteLift_cliqueIncomingFreq_eventually_eq ω i] with n hsub hout hin
  unfold finiteCliqueFrequencyBalance cliqueFrequencyBalance lift at *
  rw [hsub, hout, hin]
  rfl

lemma finiteLift_cliqueFrequencyBalance_all_eventually_eq
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) =
        E.finiteCliqueFrequencyBalance ω n i := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) =
          E.finiteCliqueFrequencyBalance ω n i := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    exact E.finiteLift_cliqueFrequencyBalance_eventually_eq ω i
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteLift_cliqueFrequencyBalance_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop, ∀ i : Fin M,
      E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
        E.cliqueFrequencyBalance ω i = 0 := by
  have h :
      ∀ᶠ n in atTop, ∀ i ∈ (Finset.univ : Finset (Fin M)),
        E.lift n (E.cliqueFrequencyBalance ω i) = 0 ↔
          E.cliqueFrequencyBalance ω i = 0 := by
    rw [(Finset.univ : Finset (Fin M)).eventually_all]
    intro i _hi
    by_cases hbal : E.cliqueFrequencyBalance ω i = 0
    · filter_upwards [E.data.finiteLift_zero_eventually_eq_zero] with n hzero
      constructor
      · intro _h
        exact hbal
      · intro _h
        rw [hbal]
        change E.data.finiteLift n (0 : E.data.Group) = 0
        exact hzero
    · filter_upwards [E.finiteLift_eventually_ne_zero hbal] with n hn
      constructor
      · intro hzero
        exact (hn hzero).elim
      · intro h
        exact (hbal h).elim
  filter_upwards [h] with n hn i
  exact hn i (by simp)

lemma finiteCliqueFrequencyBalance_all_zero_iff_eventually
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    ∀ᶠ n in atTop,
      ((∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0) ↔
        ∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0) := by
  filter_upwards
    [E.finiteLift_cliqueFrequencyBalance_all_eventually_eq ω,
      E.finiteLift_cliqueFrequencyBalance_zero_iff_eventually ω] with n heq hzero
  constructor
  · intro hfin i
    exact (hzero i).mp (by rw [heq i, hfin i])
  · intro hcompact i
    have hlift_zero : E.lift n (E.cliqueFrequencyBalance ω i) = 0 :=
      (hzero i).mpr (hcompact i)
    rwa [heq i] at hlift_zero

lemma finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ) (i : Fin M) :
    E.finiteCliqueFrequencyBalance ω n i =
      finiteEdgeFrequencyBalanceOn (cliqueEdgePairs M)
        (fun e => E.lift n (ω e)) i := by
  rfl

lemma prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1 - x e.2)))) =
      ∏ i : Fin M,
        ZMod.stdAddChar (-(E.finiteCliqueFrequencyBalance ω n i * x i)) := by
  simpa [E.finiteCliqueFrequencyBalance_eq_finiteEdgeFrequencyBalanceOn ω n] using
    prod_stdAddChar_edge_eq_prod_balance (cliqueEdgePairs M)
      (fun e => E.lift n (ω e)) x

lemma finiteCliqueAssignmentAverage_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∏ e ∈ cliqueEdgePairs M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1 - x e.2))) =
      if (∀ i : Fin M, E.finiteCliqueFrequencyBalance ω n i = 0)
      then 1 else 0 := by
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1 - x e.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ i : Fin M,
              ZMod.stdAddChar
                (-(E.finiteCliqueFrequencyBalance ω n i * x i)) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdge_eq_prod_finiteCliqueBalance ω n x]
  exact finitePiAverage_prod_stdAddChar_neg_mul_eq_if
    (fun i : Fin M => E.finiteCliqueFrequencyBalance ω n i)

lemma finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelWeight (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) x =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            ZMod.stdAddChar
              (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) := by
  classical
  unfold finiteCliqueKernelWeight
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalFinite P n (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalFinite P n (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalFinite P n (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * ZMod.stdAddChar
              (-(E.lift n γ * (x e.1.1 - x e.1.2))) by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalFinite_eq_sum_of_support_subset E P n A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_stdAddChar_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) (n : ℕ)
    (x : Fin M → ZMod (S.p (E.φ n))) [NeZero (S.p (E.φ n))] :
    (∏ e : CliqueEdgeIndex M,
        ZMod.stdAddChar
          (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
      ∏ e ∈ cliqueEdgePairs M,
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2))) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        ZMod.stdAddChar
          (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
              (x e.1 - x e.2)))))

lemma finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) (n : ℕ)
    [Fact (S.p (E.φ n)).Prime] [NeZero (S.p (E.φ n))] :
    finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
        (fun z : ZMod (S.p (E.φ n)) => TrigPoly.evalFinite P n z) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
            then 1 else 0) := by
  classical
  unfold finiteCliqueKernelDensity
  rw [show
      (∑ x : Fin M → ZMod (S.p (E.φ n)),
          finiteCliqueKernelWeight
            (fun z : ZMod (S.p (E.φ n)) =>
              TrigPoly.evalFinite P n z) x) =
        ∑ x : Fin M → ZMod (S.p (E.φ n)),
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.finiteCliqueKernelWeight_evalFinite_eq_sum_edgeAssignments_of_support_subset
          P A hP n x]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ω hω
  rw [← Finset.mul_sum]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          (E.cliqueEdgeAssignmentCoeff P ω *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) =
        E.cliqueEdgeAssignmentCoeff P ω *
          (((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
            ∑ x : Fin M → ZMod (S.p (E.φ n)),
              ∏ e : CliqueEdgeIndex M,
                ZMod.stdAddChar
                  (-(E.lift n (ω e) * (x e.1.1 - x e.1.2)))) by
        ring]
  rw [show
      ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e : CliqueEdgeIndex M,
              ZMod.stdAddChar
                (-(E.lift n (ω e) * (x e.1.1 - x e.1.2))) =
        ((Fintype.card (Fin M → ZMod (S.p (E.φ n))) : ℂ)⁻¹) *
          ∑ x : Fin M → ZMod (S.p (E.φ n)),
            ∏ e ∈ cliqueEdgePairs M,
              ZMod.stdAddChar
                (-(E.lift n (E.extendCliqueEdgeAssignment ω e) *
                    (x e.1 - x e.2))) by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro x _hx
        exact E.prod_stdAddChar_cliqueEdgeIndex_eq_extend ω n x]
  rw [E.finiteCliqueAssignmentAverage_eq_if (E.extendCliqueEdgeAssignment ω) n]

/-- Compact character product for one edge-frequency assignment, regrouped by
vertex balances. -/
lemma prod_addCharacterValue_cliqueEdge_eq_prod_balance
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2) (ω e)) =
      ∏ i : Fin M, E.addCharacterValue (x i) (E.cliqueFrequencyBalance ω i) := by
  classical
  unfold cliqueFrequencyBalance cliqueOutgoingFreq cliqueIncomingFreq
  rw [show
      (∏ i : Fin M,
          E.addCharacterValue (x i)
            ((∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.1 = i), ω e) -
              ∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
        (∏ i : Fin M,
          (∏ e ∈ cliqueEdgePairs M,
            if e.1 = i then E.addCharacterValue (x i) (ω e) else 1) *
          (∏ e ∈ cliqueEdgePairs M,
            if e.2 = i then E.addCharacterValue (x i) (-ω e) else 1)) by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        rw [sub_eq_add_neg, E.addCharacterValue_add]
        rw [E.addCharacterValue_sum]
        rw [show
            E.addCharacterValue (x i)
                (-(∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), ω e)) =
              E.addCharacterValue (x i)
                (∑ e ∈ (cliqueEdgePairs M).filter (fun e => e.2 = i), -ω e) by
              simp]
        rw [E.addCharacterValue_sum]
        rw [Finset.prod_filter, Finset.prod_filter]]
  rw [Finset.prod_mul_distrib]
  rw [prod_vertex_outgoing_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (ω e))]
  rw [prod_vertex_incoming_eq_edge_prod (cliqueEdgePairs M)
    (fun e i => E.addCharacterValue (x i) (-ω e))]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro e _he
  simp [sub_eq_add_neg, E.addCharacterValue_add_point]

lemma compactCliqueAssignmentIntegral_eq_if
    (E : CayleyExtraction S) {M : ℕ}
    (ω : Fin M × Fin M → E.Group) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.addCharacterValue (x e.1 - x e.2) (ω e))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      if (∀ i : Fin M, E.cliqueFrequencyBalance ω i = 0)
      then 1 else 0 := by
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.addCharacterValue (x e.1 - x e.2) (ω e))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∏ i : Fin M, E.addCharacterValue (x i)
            (E.cliqueFrequencyBalance ω i)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.prod_addCharacterValue_cliqueEdge_eq_prod_balance ω x]
  exact E.compactPiIntegral_prod_addCharacterValue_eq_if
    (fun i : Fin M => E.cliqueFrequencyBalance ω i)

lemma continuous_cliqueEdgeAssignmentCharacterProduct
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group) :
    Continuous (fun x : Fin M → E.CompactAddDual =>
      ∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) := by
  simpa using
    (continuous_finsetProd (Finset.univ : Finset (CliqueEdgeIndex M))
      (fun e _he =>
        (E.addCharacterValue_continuous (ω e)).comp
          ((continuous_apply e.1.1).sub (continuous_apply e.1.2))))

lemma integrable_cliqueEdgeAssignmentTerm
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (ω : CliqueEdgeIndex M → E.Group) :
    Integrable
      (fun x : Fin M → E.CompactAddDual =>
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
      (Measure.pi (fun _ : Fin M => E.haar)) :=
  (continuous_const.mul
      (E.continuous_cliqueEdgeAssignmentCharacterProduct ω)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A)
    (x : Fin M → E.CompactAddDual) :
    (∏ e ∈ cliqueEdgePairs M,
        TrigPoly.evalAdd P (x e.1 - x e.2)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          ∏ e : CliqueEdgeIndex M,
            E.addCharacterValue (x e.1.1 - x e.1.2) (ω e) := by
  classical
  rw [show
      (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2)) =
        ∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2) by
        simpa [CliqueEdgeIndex] using
          (Finset.prod_attach (s := cliqueEdgePairs M)
            (f := fun e : Fin M × Fin M =>
              TrigPoly.evalAdd P (x e.1 - x e.2))).symm]
  rw [show
      (∏ e : CliqueEdgeIndex M,
          TrigPoly.evalAdd P (x e.1.1 - x e.1.2)) =
        ∏ e : CliqueEdgeIndex M,
          ∑ γ ∈ A,
            P γ * E.addCharacterValue (x e.1.1 - x e.1.2) γ by
        refine Finset.prod_congr rfl ?_
        intro e _he
        exact TrigPoly.evalAdd_eq_sum_of_support_subset E P A hP
          (x e.1.1 - x e.1.2)]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl ?_
  intro ω _hω
  rw [Finset.prod_mul_distrib]
  rfl

lemma prod_addCharacterValue_cliqueEdgeIndex_eq_extend
    (E : CayleyExtraction S) {M : ℕ}
    (ω : CliqueEdgeIndex M → E.Group)
    (x : Fin M → E.CompactAddDual) :
    (∏ e : CliqueEdgeIndex M,
        E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)) =
      ∏ e ∈ cliqueEdgePairs M,
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e) := by
  simpa [CliqueEdgeIndex] using
    (Finset.prod_attach (s := cliqueEdgePairs M)
      (f := fun e : Fin M × Fin M =>
        E.addCharacterValue (x e.1 - x e.2)
          (E.extendCliqueEdgeAssignment ω e)))

lemma compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
    (E : CayleyExtraction S) {M : ℕ}
    (P : E.TrigPoly) (A : Finset E.Group) (hP : P.support ⊆ A) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          TrigPoly.evalAdd P (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)) =
      ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
        E.cliqueEdgeAssignmentCoeff P ω *
          (if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
            then 1 else 0) := by
  classical
  rw [show
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∫ x : Fin M → E.CompactAddDual,
          ∑ ω ∈ Fintype.piFinset (fun _ : CliqueEdgeIndex M => A),
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
          ∂Measure.pi (fun _ : Fin M => E.haar) by
        congr 1
        funext x
        exact E.compactCliqueKernel_evalAdd_eq_sum_edgeAssignments_of_support_subset
          P A hP x]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro ω _hω
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            E.cliqueEdgeAssignmentCoeff P ω *
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          E.cliqueEdgeAssignmentCoeff P ω *
            ∫ x : Fin M → E.CompactAddDual,
              ∏ e : CliqueEdgeIndex M,
                E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)
            ∂Measure.pi (fun _ : Fin M => E.haar) by
      simpa using
        (MeasureTheory.integral_const_mul
          (μ := Measure.pi (fun _ : Fin M => E.haar))
          (E.cliqueEdgeAssignmentCoeff P ω)
          (fun x : Fin M → E.CompactAddDual =>
            ∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e)))]
    rw [show
        (∫ x : Fin M → E.CompactAddDual,
            (∏ e : CliqueEdgeIndex M,
              E.addCharacterValue (x e.1.1 - x e.1.2) (ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar)) =
          ∫ x : Fin M → E.CompactAddDual,
            (∏ e ∈ cliqueEdgePairs M,
              E.addCharacterValue (x e.1 - x e.2)
                (E.extendCliqueEdgeAssignment ω e))
            ∂Measure.pi (fun _ : Fin M => E.haar) by
          congr 1
          funext x
          exact E.prod_addCharacterValue_cliqueEdgeIndex_eq_extend ω x]
    rw [E.compactCliqueAssignmentIntegral_eq_if (E.extendCliqueEdgeAssignment ω)]
  · intro ω _hω
    exact E.integrable_cliqueEdgeAssignmentTerm P ω

lemma finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
    (E : CayleyExtraction S) {M : ℕ}
    (Pseq : ℕ → E.TrigPoly) (P : E.TrigPoly) (A : Finset E.Group)
    (hPseq_support : ∀ᶠ n in atTop, (Pseq n).support ⊆ A)
    (hP_support : P.support ⊆ A)
    (hcoeff :
      ∀ γ ∈ A, Tendsto (fun n => Pseq n γ) atTop (𝓝 (P γ))) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  classical
  let W : Finset (CliqueEdgeIndex M → E.Group) :=
    Fintype.piFinset (fun _ : CliqueEdgeIndex M => A)
  let compactTerm : (CliqueEdgeIndex M → E.Group) → ℂ := fun ω =>
    E.cliqueEdgeAssignmentCoeff P ω *
      (if (∀ i : Fin M,
          E.cliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) i = 0)
        then 1 else 0)
  let finiteTerm : ℕ → (CliqueEdgeIndex M → E.Group) → ℂ := fun n ω =>
    E.cliqueEdgeAssignmentCoeff (Pseq n) ω *
      (if (∀ i : Fin M,
          E.finiteCliqueFrequencyBalance
            (E.extendCliqueEdgeAssignment ω) n i = 0)
        then 1 else 0)
  have hfinite_exp :
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (Pseq n) n z)) =ᶠ[atTop]
      (fun n => ∑ ω ∈ W, finiteTerm n ω) := by
    filter_upwards [hPseq_support] with n hn_support
    have : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
    have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
    rw [E.finiteCliqueKernelDensity_evalFinite_eq_sum_edgeAssignments_of_support_subset
      (Pseq n) A hn_support n]
  have hcompact_exp :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            TrigPoly.evalAdd P (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar)) =
        ∑ ω ∈ W, compactTerm ω := by
    rw [E.compactCliqueDensity_evalAdd_eq_sum_edgeAssignments_of_support_subset
      P A hP_support]
  have hterm :
      ∀ ω ∈ W, Tendsto (fun n => finiteTerm n ω) atTop (𝓝 (compactTerm ω)) := by
    intro ω hω
    have hω_mem : ∀ e : CliqueEdgeIndex M, ω e ∈ A :=
      Fintype.mem_piFinset.mp hω
    have hcoeff_prod :
        Tendsto (fun n => E.cliqueEdgeAssignmentCoeff (Pseq n) ω)
          atTop (𝓝 (E.cliqueEdgeAssignmentCoeff P ω)) := by
      unfold cliqueEdgeAssignmentCoeff
      exact tendsto_finsetProd (Finset.univ : Finset (CliqueEdgeIndex M))
        (fun e _he => hcoeff (ω e) (hω_mem e))
    have hif :
        (fun n =>
          if (∀ i : Fin M,
              E.finiteCliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) n i = 0)
          then (1 : ℂ) else 0) =ᶠ[atTop]
        (fun _n =>
          if (∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0)
          then (1 : ℂ) else 0) := by
      filter_upwards
        [E.finiteCliqueFrequencyBalance_all_zero_iff_eventually
          (E.extendCliqueEdgeAssignment ω)] with n hn
      by_cases hfin :
          ∀ i : Fin M,
            E.finiteCliqueFrequencyBalance
              (E.extendCliqueEdgeAssignment ω) n i = 0
      · have hcompact :
            ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 :=
          hn.mp hfin
        simp [hfin, hcompact]
      · have hcompact :
            ¬ ∀ i : Fin M,
              E.cliqueFrequencyBalance
                (E.extendCliqueEdgeAssignment ω) i = 0 := by
          intro hc
          exact hfin (hn.mpr hc)
        simp [hfin, hcompact]
    have hif_tendsto :
        Tendsto
          (fun n =>
            if (∀ i : Fin M,
                E.finiteCliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) n i = 0)
            then (1 : ℂ) else 0)
          atTop
          (𝓝
            (if (∀ i : Fin M,
                E.cliqueFrequencyBalance
                  (E.extendCliqueEdgeAssignment ω) i = 0)
              then (1 : ℂ) else 0)) :=
      tendsto_const_nhds.congr' hif.symm
    exact (hcoeff_prod.mul hif_tendsto).congr' (Filter.Eventually.of_forall fun n => rfl)
  have hsum :
      Tendsto (fun n => ∑ ω ∈ W, finiteTerm n ω)
        atTop (𝓝 (∑ ω ∈ W, compactTerm ω)) :=
    tendsto_finsetSum W hterm
  rw [hcompact_exp]
  exact hsum.congr' hfinite_exp.symm

lemma finiteSmoothModelTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) (n : ℕ) :
    (E.finiteSmoothModelTrigPoly Q n).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.finiteSmoothModelTrigPoly Q n γ = 0 := by
    rw [E.finiteSmoothModelTrigPoly_apply Q n γ, hfejer]
    simp
  exact hγ hzero

lemma compactSmoothTrigPoly_support_subset_fejer
    (E : CayleyExtraction S) (Q : Finset E.Group) :
    (E.compactSmoothTrigPoly Q).support ⊆
      (E.fejerTrigPoly Q).support := by
  intro γ hγ
  rw [Finsupp.mem_support_iff] at hγ ⊢
  intro hfejer
  have hzero : E.compactSmoothTrigPoly Q γ = 0 := by
    rw [E.compactSmoothTrigPoly_apply Q γ, hfejer]
    simp
  exact hγ hzero

lemma finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (fun z : ZMod (S.p (E.φ n)) =>
            TrigPoly.evalFinite (E.finiteSmoothModelTrigPoly Q n) n z))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  simpa [compactSmooth] using
    E.finiteCliqueKernelDensity_evalFinite_tendsto_compact_of_coeff_tendsto
      (fun n => E.finiteSmoothModelTrigPoly Q n)
      (E.compactSmoothTrigPoly Q)
      (E.fejerTrigPoly Q).support
      (Filter.Eventually.of_forall
        (fun n => E.finiteSmoothModelTrigPoly_support_subset_fejer Q n))
      (E.compactSmoothTrigPoly_support_subset_fejer Q)
      (fun γ _hγ =>
        E.finiteSmoothModelTrigPoly_apply_tendsto_compactSmoothTrigPoly Q γ)

lemma finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
        letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
        finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n))
      atTop
      (𝓝
        (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂Measure.pi (fun _ : Fin M => E.haar))) := by
  refine
    (E.finiteCliqueKernelDensity_finiteSmoothModelTrigPoly_tendsto_compactSmooth
      Q M).congr' ?_
  filter_upwards
    [E.finiteSmooth_eq_evalFinite_finiteSmoothModelTrigPoly_eventually Q]
    with n hn
  have : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
  have : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
  congr 1
  funext z
  exact (hn z).symm

lemma compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar)).re =
      continuousCliqueDensity E.haar M (E.compactSmoothReal Q) := by
  classical
  let μ : Measure (Fin M → E.CompactAddDual) :=
    Measure.pi (fun _ : Fin M => E.haar)
  have hprod :
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2)) =
      (fun x : Fin M → E.CompactAddDual =>
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    funext x
    calc
      (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
          =
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            refine Finset.prod_congr rfl ?_
            intro e _he
            exact E.compactSmooth_eq_ofReal_compactSmoothReal Q
              (x e.1 - x e.2)
      _ =
        ((∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) := by
            simp
  have hintegral :
      (∫ x : Fin M → E.CompactAddDual,
          (∏ e ∈ cliqueEdgePairs M,
            E.compactSmooth Q (x e.1 - x e.2))
          ∂μ) =
        ∫ x : Fin M → E.CompactAddDual,
          ((∏ e ∈ cliqueEdgePairs M,
            E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ := by
    rw [hprod]
  have hcont :
      Continuous (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) := by
    refine continuous_finsetProd (cliqueEdgePairs M) ?_
    intro e _he
    exact Complex.continuous_ofReal.comp
      ((E.compactSmoothReal_continuous Q).comp
        ((continuous_apply e.1).sub (continuous_apply e.2)))
  have hint :
      Integrable
        (fun x : Fin M → E.CompactAddDual =>
          ∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hintegral]
  change RCLike.re
      (∫ x : Fin M → E.CompactAddDual,
        ∏ e ∈ cliqueEdgePairs M,
          ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ) ∂μ) =
    continuousCliqueDensity E.haar M (E.compactSmoothReal Q)
  refine (integral_re (μ := μ) (f := fun x : Fin M → E.CompactAddDual =>
    ∏ e ∈ cliqueEdgePairs M,
      ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ)) hint).symm.trans ?_
  have hre_fun :
      (fun x : Fin M → E.CompactAddDual =>
        RCLike.re
          (∏ e ∈ cliqueEdgePairs M,
            ((E.compactSmoothReal Q (x e.1 - x e.2)) : ℂ))) =
      (fun x : Fin M → E.CompactAddDual =>
        ∏ e ∈ cliqueEdgePairs M,
          E.compactSmoothReal Q (x e.1 - x e.2)) := by
    funext x
    have hprod_cast :=
      (Complex.ofReal_prod (cliqueEdgePairs M)
        (fun e : Fin M × Fin M =>
          E.compactSmoothReal Q (x e.1 - x e.2))).symm
    rw [hprod_cast]
    exact Complex.ofReal_re _
  rw [hre_fun]
  simp [continuousCliqueDensity, continuousCliqueKernel,
    continuousCliqueEdgePairs, cliqueEdgePairs, μ]

lemma finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
    (E : CayleyExtraction S) (Q : Finset E.Group) (M : ℕ) :
    Tendsto
      (fun n =>
        (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
         letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
         finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := M)
          (E.finiteSmooth Q n)).re)
      atTop
      (𝓝 (continuousCliqueDensity E.haar M (E.compactSmoothReal Q))) := by
  have hcomplex :=
    E.finiteCliqueKernelDensity_finiteSmooth_tendsto_compactSmooth Q M
  have hre :=
    (Complex.continuous_re.tendsto
      (∫ x : Fin M → E.CompactAddDual,
        (∏ e ∈ cliqueEdgePairs M,
          E.compactSmooth Q (x e.1 - x e.2))
        ∂Measure.pi (fun _ : Fin M => E.haar))).comp hcomplex
  simpa [Function.comp_def,
    E.compactSmooth_cliqueDensity_integral_re_eq_continuousCliqueDensity Q M]
    using hre

end CayleyExtraction

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Contradiction.lean
    ============================================================= -/

/-
Erdős Problem 42 — contradiction from a compact-Cayley counterexample sequence.
-/

namespace Erdos42.CompactCayley

open Filter Erdos42
open scoped Topology

noncomputable section

theorem CayleyCounterSeq.false
    {ℓ : ℕ} {η : ℝ} (hℓ : 2 ≤ ℓ) (hη : 0 < η)
    (S : CayleyCounterSeq ℓ η) :
    False := by
  classical
  obtain ⟨E, _⟩ := exists_cayleyExtraction S
  let ρ : ℝ := continuousCliqueDensity E.haar ℓ E.fReal
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact E.compact_limit_cliqueDensity_pos hℓ hη
  let L : ℝ := ((ℓ * ℓ : ℕ) : ℝ)
  have hℓ_pos : 0 < ℓ := by omega
  have hL_pos : 0 < L := by
    dsimp [L]
    exact_mod_cast Nat.mul_pos hℓ_pos hℓ_pos
  have htarget_pos : 0 < ρ / (8 * L) := by
    exact div_pos hρ_pos (mul_pos (by norm_num) hL_pos)
  obtain ⟨qNat, hqNat_pos, hqNat_inv⟩ :=
    Real.exists_nat_pos_inv_lt htarget_pos
  let q : ℕ+ := ⟨qNat, hqNat_pos⟩
  let qinv : ℝ := ((q : ℝ)⁻¹ : ℝ)
  have hq_pos_real : 0 < (q : ℝ) := by
    exact_mod_cast q.pos
  have hqinv_pos : 0 < qinv := by
    dsimp [qinv]
    exact inv_pos.mpr hq_pos_real
  have hqinv_lt : qinv < ρ / (8 * L) := by
    simpa [q, qinv] using hqNat_inv
  have hq_margin : L * (2 * qinv) < ρ / 4 := by
    have hmul :
        (2 * L) * qinv < (2 * L) * (ρ / (8 * L)) :=
      mul_lt_mul_of_pos_left hqinv_lt (mul_pos (by norm_num) hL_pos)
    have hcalc : (2 * L) * (ρ / (8 * L)) = ρ / 4 := by
      field_simp [ne_of_gt hL_pos]
      ring
    nlinarith
  let Bextra : Finset E.Group :=
    (E.data.largeSpectrumGenerators q).image Neg.neg
  obtain ⟨Q, hQ, hlower, _hQdensity_pos, hQdensity_ge⟩ :=
    E.exists_compactSmoothReal_cliqueDensity_pos_and_fejerPairCoeffLowerBound
      hℓ hη Bextra hqinv_pos
  let Merr : ℝ := max (2 * qinv) qinv
  have hMerr_eq : Merr = 2 * qinv := by
    dsimp [Merr]
    exact max_eq_left (by nlinarith [le_of_lt hqinv_pos])
  have hMerr_nonneg : 0 ≤ Merr := by
    rw [hMerr_eq]
    positivity
  have hMerr_margin : L * Merr < ρ / 4 := by
    simpa [Merr, hMerr_eq] using hq_margin
  have hthreshold_lt_limit :
      L * Merr <
        continuousCliqueDensity E.haar ℓ (E.compactSmoothReal Q) := by
    have hquarter_half : ρ / 4 < ρ / 2 := by nlinarith
    exact lt_of_lt_of_le (lt_trans hMerr_margin hquarter_half)
      (by simpa [ρ] using hQdensity_ge)
  have hdensity_eventually :
      ∀ᶠ n in atTop,
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re := by
    have hconv :=
      E.finiteCliqueKernelDensity_finiteSmooth_re_tendsto_compactSmoothReal
        Q ℓ
    exact hconv.eventually (isOpen_Ioi.mem_nhds hthreshold_lt_limit)
  have hnorm_eventually := E.finiteSmooth_norm_le_one_eventually Q hQ
  have hspectral_eventually :
      ∀ᶠ n in atTop,
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) := by
    have hspec :=
      E.spectralBound_indicator_sub_finiteSmooth_eventually_of_lowerBound_neg
        q Q hQ hlower
    refine hspec.mono ?_
    intro n hn
    simpa [Merr, qinv] using hn
  have hall :
      ∀ᶠ n in atTop,
        (∀ z : ZMod (S.p (E.φ n)), ‖E.finiteSmooth Q n z‖ ≤ 1) ∧
        (letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩;
          SpectralBound
            (fun z : ZMod (S.p (E.φ n)) =>
              indicatorC (S.T (E.φ n)) z - E.finiteSmooth Q n z)
            Merr) ∧
        L * Merr <
          (letI : Fact (S.p (E.φ n)).Prime := ⟨S.prime (E.φ n)⟩
           letI : NeZero (S.p (E.φ n)) := ⟨(S.prime (E.φ n)).ne_zero⟩
           finiteCliqueKernelDensity (p := S.p (E.φ n)) (ℓ := ℓ)
            (E.finiteSmooth Q n)).re :=
    hnorm_eventually.and (hspectral_eventually.and hdensity_eventually)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  rcases hN N le_rfl with ⟨hnorm, hspectral, hdensity⟩
  have : Fact (S.p (E.φ N)).Prime := ⟨S.prime (E.φ N)⟩
  have : NeZero (S.p (E.φ N)) := ⟨(S.prime (E.φ N)).ne_zero⟩
  have hdensity' :
      ((ℓ * ℓ : ℕ) : ℝ) * Merr <
        (finiteCliqueKernelDensity (p := S.p (E.φ N)) (ℓ := ℓ)
          (E.finiteSmooth Q N)).re := by
    simpa [L] using hdensity
  have hclique :
      ∃ C : Finset (ZMod (S.p (E.φ N))),
        C.card = ℓ ∧ CliqueInCayley (S.T (E.φ N)) C :=
    exists_clique_of_spectral_density_transfer_sq
      (T := S.T (E.φ N))
      (g := E.finiteSmooth Q N)
      (M := Merr)
      (S.T_sym (E.φ N))
      (S.T_zero (E.φ N))
      hMerr_nonneg
      hnorm
      hspectral
      hdensity'
  exact S.no_clique (E.φ N) hclique

end

end Erdos42.CompactCayley

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/CliqueAxiom.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B trust boundary: compact Cayley clique theorem.

Theorem 2.1 of `erdos42_compact_sidon_clean.pdf` (Google Drive link in
`forum.md`). A dense symmetric Cayley graph on `ZMod p`, with `0 ∉ T`
and small nontrivial Fourier coefficients (upper bound), contains a clique of
any prescribed size for all sufficiently large primes.

Mathematically: classical, unconditional. The compact-Cayley PDF proves it via
Fourier extraction (Lemma 2.2), equidistribution of finite lifts (2.3), basic
limit properties (2.4), spectral cut-norm control (2.5), counting convergence
(2.6), and clique forcing on connected compact groups (2.7).

This file now closes the former Route B trust boundary by deriving the compact
Cayley clique theorem from the assumption-free countersequence contradiction.
-/

namespace Erdos42

namespace CompactCayley

/-- **Compact Cayley clique theorem (compact PDF Theorem 2.1).** Trust
boundary for Route B. For every clique size `ℓ ≥ 2` and every density `η > 0`,
there exists `ε > 0` such that for all sufficiently large primes `p`, every
symmetric `T ⊆ ZMod p` with `0 ∉ T`, density `≥ η`, and Fourier upper bound
`≤ ε` (at every nontrivial character) contains an `ℓ`-clique in its Cayley
graph. -/
theorem compact_cayley_clique
    (ℓ : ℕ) (η : ℝ) (_hℓ : 2 ≤ ℓ) (_hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ p₀ : ℕ, ∀ p : ℕ, [Fact p.Prime] → p₀ < p →
    ∀ T : Finset (ZMod p),
      SymmetricFinset T →
      (0 : ZMod p) ∉ T →
      η * (p : ℝ) ≤ (T.card : ℝ) →
      FourierUpperIndicator T ε →
      ∃ C : Finset (ZMod p),
        C.card = ℓ ∧ CliqueInCayley T C := by
  classical
  by_contra hfail
  have hexplicit_fail : ¬ CompactCayleyCliqueStatementExplicit ℓ η := by
    intro hexplicit
    exact hfail (compactCayleyCliqueStatement_from_explicit hexplicit)
  obtain ⟨S, _⟩ :=
    exists_cayleyCounterSeq_of_not_compactCayleyCliqueStatementExplicit
      hexplicit_fail
  exact S.false _hℓ _hη

end CompactCayley

end Erdos42

/-! =============================================================
    Section from: Erdos/P42/CompactCayley/Main.lean
    ============================================================= -/

/-
Erdős Problem 42 — Route B final assembly.

This is the compact-Cayley downstream file that imports the proved
`compact_cayley_clique` theorem. The finite allowed-difference Fourier
estimates and greedy Sidon extraction stay in `FiniteReduction.lean`, outside
the compact-Cayley namespace, so Route A can reuse them independently.
-/

namespace Erdos42.CompactCayley

open Finset Erdos42

/-! ## Final assembly: Theorem 1.1 from `compact_cayley_clique` -/

/-- **Theorem 1.1, Route B.** For every `M ≥ 1`, there is `N₀` such that for
all `N ≥ N₀` and every non-empty Sidon `A ⊆ [1, N] ⊂ ℤ`, there is a Sidon
`B ⊆ [1, N]` with `|B| = M` and no nonzero common difference, using the
proved compact-Cayley clique theorem. -/
theorem theorem_1_1_from_compact_cayley
    (M : ℕ) (_hM : 1 ≤ M) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℤ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ (N : ℤ)) → IsSidonInt A → A.Nonempty →
        ∃ B : Finset ℤ,
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ (N : ℤ)) ∧
          IsSidonInt B ∧ B.card = M ∧
          AvoidsNonzeroDiff A B := by
  classical
  let R := greedySidonThreshold M
  have hRpos : 0 < R := by
    dsimp [R, greedySidonThreshold]
    omega
  have hCliqueSize : 2 ≤ 8 * R := by omega
  obtain ⟨ε, hεpos, p₀, hcompact⟩ :=
    compact_cayley_clique (8 * R) (1 / 2 : ℝ) hCliqueSize (by norm_num)
  obtain ⟨Nε, hNε⟩ := sidon_card_minus_one_div_prime_eventually_small ε hεpos
  refine ⟨max (p₀ + 1) Nε, ?_⟩
  intro N hN A hAint hSidon _hAnonempty
  have hNpos : 0 < N := by omega
  obtain ⟨p, hpprime, hpgt, hple⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  have : Fact p.Prime := ⟨hpprime⟩
  have hp₀lt : p₀ < p := by omega
  have hpN : N < p := by omega
  have hpupper : p < 8 * N := by
    have hple' : p ≤ 8 * N := by omega
    have hpne2 : p ≠ 2 := by omega
    have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
    have hpne : p ≠ 8 * N := by
      intro hpeq
      have heven : Even p := by
        rw [hpeq, even_iff_two_dvd]
        exact ⟨4 * N, by ring⟩
      exact (Nat.not_even_iff_odd.mpr hpodd) heven
    omega
  let T : Finset (ZMod p) := allowedDiffSetMod p A
  have hT_sym : SymmetricFinset T := by
    simpa [T] using allowedDiffSetMod_symmetric p A
  have hT_zero : (0 : ZMod p) ∉ T := by
    simpa [T] using zero_notMem_allowedDiffSetMod p A
  have hT_density : (1 / 2 : ℝ) * p ≤ (T.card : ℝ) := by
    simpa [T] using allowedDiffSetMod_density (p := p) (N := N) hpgt A hAint hSidon
  have hsmall : ((A.card - 1 : ℕ) : ℝ) / p ≤ ε :=
    hNε N p (by omega) hpgt A hAint hSidon
  have hT_fourier : FourierUpperIndicator T ε := by
    simpa [T] using
      allowedDiffs_fourier_upper (p := p) (N := N) hpgt A hAint hSidon ε hsmall
  obtain ⟨C, hCcard, hCclique⟩ :=
    hcompact p hp₀lt T hT_sym hT_zero hT_density hT_fourier
  obtain ⟨s, hs⟩ :=
    exists_large_intersection_cyclicInterval (p := p) (N := N) (R := R)
      hpN C (by simpa [R] using hCcard) hpupper
  let X : Finset ℤ := intervalLiftSet p N s C
  have hXcard : R ≤ X.card := by
    dsimp [X]
    rw [intervalLiftSet_card_eq hpN]
    exact hs
  obtain ⟨B, hBX, hBcard, hBsidon⟩ := exists_sidon_subset_of_card_ge M X hXcard
  refine ⟨B, ?_, hBsidon, hBcard, ?_⟩
  · intro b hb
    rcases mem_intervalLiftSet.mp (hBX hb) with ⟨i, hiN, _hiC, rfl⟩
    constructor <;> omega
  · intro d hdA hdB
    rw [mem_diffFinset] at hdA hdB
    rcases hdA with ⟨a₁, ha₁, a₂, ha₂, rfl⟩
    rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
    by_cases hzero : a₁ - a₂ = 0
    · exact hzero
    · exfalso
      rcases mem_intervalLiftSet.mp (hBX hb₁) with ⟨i₁, hi₁N, hi₁C, hb₁eq⟩
      rcases mem_intervalLiftSet.mp (hBX hb₂) with ⟨i₂, hi₂N, hi₂C, hb₂eq⟩
      have hbne : b₁ ≠ b₂ := by
        intro hb
        apply hzero
        rw [hb] at hbDiff
        linarith
      have hine : i₁ ≠ i₂ := by
        intro hi
        apply hbne
        rw [hb₁eq, hb₂eq, hi]
      let y₁ : ZMod p := s + (i₁ : ZMod p)
      let y₂ : ZMod p := s + (i₂ : ZMod p)
      have hyne : y₁ ≠ y₂ := by
        intro hy
        apply hine
        apply nat_eq_of_zmod_eq_of_lt
          (Nat.lt_trans hi₁N hpN) (Nat.lt_trans hi₂N hpN)
        apply add_left_cancel (a := s)
        simpa [y₁, y₂] using hy
      have hallowed : y₁ - y₂ ∈ T := hCclique y₁ hi₁C y₂ hi₂C hyne
      have hyDiff : y₁ - y₂ = ((a₁ - a₂ : ℤ) : ZMod p) := by
        calc
          y₁ - y₂ = (i₁ : ZMod p) - (i₂ : ZMod p) := by
            simp [y₁, y₂]
          _ = ((b₁ - b₂ : ℤ) : ZMod p) := by
            rw [hb₁eq, hb₂eq]
            norm_num
          _ = ((a₁ - a₂ : ℤ) : ZMod p) := by
            rw [hbDiff]
      have hcast : ((a₁ - a₂ : ℤ) : ZMod p) ∈ allowedDiffSetMod p A := by
        simpa [T, hyDiff] using hallowed
      rw [allowedDiffSetMod, Finset.mem_filter] at hcast
      exact hcast.2.2 a₁ ha₁ a₂ ha₂ rfl

end Erdos42.CompactCayley

/-! =============================================================
    FC bridge: public `Set ℕ` wrapper + FC iff form (Route B)
    ============================================================= -/

namespace Erdos42

open Filter Set
open scoped Pointwise

/-! ## §1 FC-aligned Sidon predicate over `Set ℕ` -/

/-- `A ⊆ ℕ` is Sidon iff every additive collision is trivial. Matches the FC
skeleton's definition. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

/-! ## §2 Bridge `Finset ℤ` ↔ `Set ℕ` for Sidon sets in `[1, N]` -/

theorem isSidonInt_of_isSidon
    {A : Set ℕ} {N : ℕ} (hA : A ⊆ Set.Icc 1 N) (hSidon : IsSidon A) :
    ∃ A' : Finset ℤ,
      (∀ a ∈ A', 1 ≤ a ∧ a ≤ (N : ℤ)) ∧ IsSidonInt A' ∧
      (A.ncard = A'.card) ∧
      (∀ x : ℕ, x ∈ A ↔ ((x : ℤ) ∈ A')) := by
  classical
  let An : Finset ℕ := (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
  let A' : Finset ℤ := An.image (fun n : ℕ => (n : ℤ))
  have hAn_mem : ∀ x : ℕ, x ∈ An ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A) at hx
      rw [Finset.mem_filter] at hx
      exact hx.2
    · intro hx
      have hxIcc : x ∈ Finset.Icc 1 N := by
        rw [Finset.mem_Icc]
        exact hA hx
      change x ∈ (Finset.Icc 1 N).filter (fun n : ℕ => n ∈ A)
      rw [Finset.mem_filter]
      exact ⟨hxIcc, hx⟩
  have hA'_mem_nat : ∀ x : ℕ, ((x : ℤ) ∈ A') ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ)) at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyx_nat : y = x := by exact_mod_cast hyx
      rw [← hyx_nat]
      exact (hAn_mem y).mp hy
    · intro hx
      change (x : ℤ) ∈ An.image (fun n : ℕ => (n : ℤ))
      rw [Finset.mem_image]
      exact ⟨x, (hAn_mem x).mpr hx, rfl⟩
  refine ⟨A', ?_, ?_, ?_, ?_⟩
  · intro a ha
    change a ∈ An.image (fun n : ℕ => (n : ℤ)) at ha
    rw [Finset.mem_image] at ha
    rcases ha with ⟨x, hx, rfl⟩
    have hxA : x ∈ A := (hAn_mem x).mp hx
    exact_mod_cast hA hxA
  · intro a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ hsum
    change a₁ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₁
    change a₂ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₂
    change a₃ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₃
    change a₄ ∈ An.image (fun n : ℕ => (n : ℤ)) at ha₄
    rw [Finset.mem_image] at ha₁ ha₂ ha₃ ha₄
    rcases ha₁ with ⟨n₁, hn₁, rfl⟩
    rcases ha₂ with ⟨n₂, hn₂, rfl⟩
    rcases ha₃ with ⟨n₃, hn₃, rfl⟩
    rcases ha₄ with ⟨n₄, hn₄, rfl⟩
    have hsum_nat : n₁ + n₂ = n₃ + n₄ := by exact_mod_cast hsum
    rcases hSidon ((hAn_mem n₁).mp hn₁) ((hAn_mem n₂).mp hn₂)
        ((hAn_mem n₃).mp hn₃) ((hAn_mem n₄).mp hn₄) hsum_nat with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · have hAset : A = (An : Set ℕ) := by
      ext x
      exact (hAn_mem x).symm
    have hAcard : A.ncard = An.card := by
      rw [hAset, Set.ncard_coe_finset]
    have hA'card : A'.card = An.card := by
      change (An.image (fun n : ℕ => (n : ℤ))).card = An.card
      apply Finset.card_image_of_injOn
      intro x _hx y _hy hxy
      exact Int.ofNat_injective hxy
    exact hAcard.trans hA'card.symm
  · intro x
    exact (hA'_mem_nat x).symm

/-! ## §3 Theorem 1.1 (Set ℕ form, Route B) -/

theorem theorem_1_1_via_cayley :
    ∀ M : ℕ, 1 ≤ M → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 N → IsSidon A → A.Nonempty →
        ∃ B : Set ℕ, B ⊆ Set.Icc 1 N ∧ IsSidon B ∧ B.ncard = M ∧
          ((A - A) ∩ (B - B) : Set ℕ) = {0} := by
  intro M hM
  classical
  obtain ⟨N₀, hN₀⟩ := CompactCayley.theorem_1_1_from_compact_cayley M hM
  refine ⟨N₀, ?_⟩
  intro N hN A hAint hSidon hAnonempty
  obtain ⟨A', hA'int, hA'sidon, _hAcard, hA'mem⟩ :=
    isSidonInt_of_isSidon (A := A) (N := N) hAint hSidon
  have hA'nonempty : A'.Nonempty := by
    obtain ⟨a, ha⟩ := hAnonempty
    exact ⟨(a : ℤ), (hA'mem a).mp ha⟩
  obtain ⟨B', hB'int, hB'sidon, hB'card, hAvoid⟩ :=
    hN₀ N hN A' hA'int hA'sidon hA'nonempty
  let Bn : Finset ℕ := B'.image Int.toNat
  let B : Set ℕ := (Bn : Set ℕ)
  have hB'_nonneg : ∀ b ∈ B', 0 ≤ b := by
    intro b hb
    exact le_trans (by norm_num) (hB'int b hb).1
  have hB'_mem_nat : ∀ x : ℕ, x ∈ B ↔ ((x : ℤ) ∈ B') := by
    intro x
    constructor
    · intro hx
      change x ∈ Bn at hx
      change x ∈ B'.image Int.toNat at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨z, hz, hzx⟩
      have hz_nonneg : 0 ≤ z := hB'_nonneg z hz
      have hz_cast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz_nonneg
      rw [← hzx, hz_cast]
      exact hz
    · intro hx
      change x ∈ Bn
      change x ∈ B'.image Int.toNat
      rw [Finset.mem_image]
      refine ⟨(x : ℤ), hx, ?_⟩
      simp
  have hBn_card : Bn.card = B'.card := by
    change (B'.image Int.toNat).card = B'.card
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx_nonneg : 0 ≤ x := hB'_nonneg x hx
    have hy_nonneg : 0 ≤ y := hB'_nonneg y hy
    calc
      x = (x.toNat : ℤ) := (Int.toNat_of_nonneg hx_nonneg).symm
      _ = (y.toNat : ℤ) := by rw [hxy]
      _ = y := Int.toNat_of_nonneg hy_nonneg
  have hBn_cardM : Bn.card = M := by
    rw [hBn_card, hB'card]
  have hB_nonempty : B.Nonempty := by
    have hBn_pos : 0 < Bn.card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hBn_pos
    exact ⟨b, hb⟩
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro b hb
    have hb' : (b : ℤ) ∈ B' := (hB'_mem_nat b).mp hb
    have hb_bounds := hB'int (b : ℤ) hb'
    exact_mod_cast hb_bounds
  · intro b₁ hb₁ b₂ hb₂ b₃ hb₃ b₄ hb₄ hsum
    have hb₁' : (b₁ : ℤ) ∈ B' := (hB'_mem_nat b₁).mp hb₁
    have hb₂' : (b₂ : ℤ) ∈ B' := (hB'_mem_nat b₂).mp hb₂
    have hb₃' : (b₃ : ℤ) ∈ B' := (hB'_mem_nat b₃).mp hb₃
    have hb₄' : (b₄ : ℤ) ∈ B' := (hB'_mem_nat b₄).mp hb₄
    have hsum_int : (b₁ : ℤ) + (b₂ : ℤ) = (b₃ : ℤ) + (b₄ : ℤ) := by
      exact_mod_cast hsum
    rcases hB'sidon hb₁' hb₂' hb₃' hb₄' hsum_int with h | h
    · exact Or.inl ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    · exact Or.inr ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [Set.ncard_coe_finset, hBn_cardM]
  · ext d
    constructor
    · intro hd
      rw [Set.mem_inter_iff] at hd
      rcases hd with ⟨hdA, hdB⟩
      rw [Set.mem_sub] at hdA hdB
      rcases hdA with ⟨a₁, ha₁, a₂, ha₂, haDiff⟩
      rcases hdB with ⟨b₁, hb₁, b₂, hb₂, hbDiff⟩
      rw [Set.mem_singleton_iff]
      by_cases hd0 : d = 0
      · exact hd0
      · exfalso
        have hDiffA_int : (a₁ : ℤ) - (a₂ : ℤ) = (d : ℤ) := by omega
        have hDiffB_int : (b₁ : ℤ) - (b₂ : ℤ) = (d : ℤ) := by omega
        have hdA' : (d : ℤ) ∈ DiffFinset A' A' := by
          rw [mem_diffFinset]
          exact ⟨(a₁ : ℤ), (hA'mem a₁).mp ha₁, (a₂ : ℤ), (hA'mem a₂).mp ha₂,
            hDiffA_int⟩
        have hdB' : (d : ℤ) ∈ DiffFinset B' B' := by
          rw [mem_diffFinset]
          exact ⟨(b₁ : ℤ), (hB'_mem_nat b₁).mp hb₁, (b₂ : ℤ), (hB'_mem_nat b₂).mp hb₂,
            hDiffB_int⟩
        have hd_int_zero : (d : ℤ) = 0 := hAvoid (d : ℤ) hdA' hdB'
        have : d = 0 := by exact_mod_cast hd_int_zero
        exact hd0 this
    · intro hd
      rw [Set.mem_singleton_iff] at hd
      subst d
      rw [Set.mem_inter_iff]
      constructor
      · rw [Set.mem_sub]
        obtain ⟨a, ha⟩ := hAnonempty
        exact ⟨a, ha, a, ha, by simp⟩
      · rw [Set.mem_sub]
        obtain ⟨b, hb⟩ := hB_nonempty
        exact ⟨b, hb, b, hb, by simp⟩

/-! ## §4 FC form (Route B) -/

/-! ## §5 FC-shape variant (matches FC's `∃ᵉ` and FC's local Sidon predicates) -/

namespace FormalConjecturesShape

universe u

/-- FC-shaped Sidon predicate. Definitionally equal to `Erdos42.IsSidon`. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ ⦃a₁⦄, a₁ ∈ A → ∀ ⦃a₂⦄, a₂ ∈ A → ∀ ⦃a₃⦄, a₃ ∈ A → ∀ ⦃a₄⦄, a₄ ∈ A →
    a₁ + a₂ = a₃ + a₄ → (a₁ = a₃ ∧ a₂ = a₄) ∨ (a₁ = a₄ ∧ a₂ = a₃)

end FormalConjecturesShape

end Erdos42

-- Quot.sound]
-- Classical.choice, Quot.sound]
-- Classical.choice, Quot.sound]

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` -/

section

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
private theorem _root_.Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Sobolev.lean` -/

section

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  ext x ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  ext v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := by
  simpa [deriv_scale'] using hasDerivAt (f.scale R) x

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
      have hderiv : ⇑(SchwartzMap.derivCLM ℝ ℂ f) = _root_.deriv (f : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply (𝕜 := ℝ) (F := ℂ) f x
      simpa [iteratedDeriv_succ', hderiv] using
        ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

set_option maxHeartbeats 800000 in
-- The dominated-convergence proof below needs more heartbeats in Lean 4.32.
theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h', CS.deriv_scale'] using
      (CS.hasDerivAt_scale (g : CS 2 ℝ) R v).const_sub 1
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1]
        convert (l5.add l7).deriv using 1
        · congr 1
        · ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g.toFun =ᶠ[𝓝 0] 0
        refine g.zero.deriv.trans ?_
        simp
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g'.toFun =ᶠ[𝓝 0] 0
        refine evg'.deriv.trans ?_
        simp
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · rw [Filter.ZeroAtFilter]
        simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Fourier.lean` -/

section

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp z.norm_coe

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by
      simp only [Circle.norm_coe, one_add_one_eq_two]
      exact le_rfl)⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  simpa [Function.comp_def, e, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_fourierChar (-x * u)).scomp x l2

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourier_real_eq, ← integral_const_mul, Real.fourierChar, Circle.exp,
    ← smul_mul_assoc, mul_smul_comm]

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Defs.lean` -/

section

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Λ n : ℝ) / n

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε

lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` -/

section

open Filter Topology

section
open Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

-- to replace existing `isLittleO_const_id_atTop`

-- to replace existing `isLittleO_const_id_atBot`

private theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

private theorem _root_.Asymptotics.IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` -/

section

section
open Function

variable {α : Type*} [Zero α]

private theorem _root_.Function.support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

private theorem _root_.Function.support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/SmoothExistence.lean` -/

section
set_option lang.lemmaCmd true

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]

lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Wiener.lean` -/

section
set_option lang.lemmaCmd true
set_option backward.isDefEq.respectTransparency false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

@[simp] lemma W21.ofCS2_toFun (ψ : CS 2 ℂ) : (W21.ofCS2 ψ).toFun = ψ.toFun := rfl

@[simp] lemma W21.ofCS2_apply (ψ : CS 2 ℂ) (x : ℝ) : (W21.ofCS2 ψ : W21) x = ψ x := rfl

@[simp] lemma W21.sub_toFun (f g : W21) : (f - g).toFun = f.toFun - g.toFun := rfl

noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

set_option backward.isDefEq.respectTransparency false in
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp

@[continuity]
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩

attribute [fun_prop] measurable_coe_nnreal_ennreal

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- TODO: find out why fun_prop does not play well with Multiplicative.ofAdd
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      Multiplicative.ofAdd, Equiv.coe_fn_mk, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

set_option backward.isDefEq.respectTransparency false in
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]

  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    rw [AddChar.coe_mk, Submonoid.mk_smul, smul_eq_mul]
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx

lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

set_option backward.isDefEq.respectTransparency false in
@[continuity, fun_prop] lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa [div_eq_mul_inv] using (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)

lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simp only [LSeries.term, h, ↓reduceIte]
      exact continuous_const.div₀
        (continuous_const.cpow (by fun_prop) (fun x => by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- TODO nnabla is redundant -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

end nabla

private lemma _root_.Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, Finset.sum_range_add, Finset.sum_range_one, add_comm 1] ; rfl

private lemma _root_.Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  change cumsum (a * b) (n + 1) =
    cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * (fun i => b (i + 1) - b i)) n
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

private lemma _root_.Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one, eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := by omega
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift, cumsum] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

private lemma _root_.Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

private lemma _root_.Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by
        simpa [Function.comp_def] using
          (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

private lemma _root_.Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
@[local gcongr]
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    gcongr

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    change nabla d =O[atTop] (fun n => (Real.log n) ^ 2)
    simpa [d] using (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a, div_eq_mul_inv] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)

set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext ; congr ; ext
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    congr
    rw [← neg_mul] ; congr ; norm_cast ; field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm

lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩

noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    have hpow := l4.pow 2
    have hpow' : HasDerivAt ((fun t : ℝ => a * log t) ^ 2)
        (2 * a ^ 2 * t⁻¹ * log t) t := hpow.congr_deriv (by ring)
    exact hpow'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.pow_apply])
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    have hprod := (hasDerivAt_id' t).mul l2
    have hprod' : HasDerivAt (((fun x : ℝ => x) * fun t => 1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t := by
      apply hprod.congr_deriv
      rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = 2 * a ^ 2 * log t by
        rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = (t * t⁻¹) * (2 * a ^ 2 * log t) by ring]
        rw [mul_inv_cancel₀ ht, one_mul]]
      simp only [pp]
      ring
    have hprod'' : HasDerivAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t :=
      hprod'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.mul_apply])
    exact hprod''.congr_deriv (by
      simp only [pp]
      ring)
  change HasDerivAt (fun t : ℝ => (t * (1 + (a * log t) ^ 2))⁻¹) (hh' a t) t
  apply (l1.inv e1).congr_deriv
  simp only [hh', pp, hh]
  field_simp [inv_eq_one_div, e1, ht]
  ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · have : 0 < 1 / (2 * π) := by positivity
    linarith
  · rw [div_lt_iff₀ (by positivity : 0 < 2 * π)]
    have hπ : (2 : ℝ) ≤ π := two_le_pi
    nlinarith

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa [cumsum] using hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    have hcomm :
        (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    rw [hcomm]
    refine le_of_eq ?_
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 =>
      convert cancel_aux' hf hg hf' hg' (n + 2) using 1
      · simp [cumsum, Finset.sum_range_succ, add_comm, add_left_comm]
      · simp [cumsum_succ, Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm]
        ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by
      simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact _root_.add_le_add l1 l3
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have hder :
        HasDerivAt (fun t => log (t / c)) ((x / c)⁻¹ * (1 / c)) x :=
      @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _
        (l3 (x / c) (by positivity)) (l4 x)
    have heq : c / x * c⁻¹ = x⁻¹ := by
      field_simp [hc.ne', hx.ne']
    simpa [heq] using hder
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    have hder := (l1 x hx).const_mul (a * c / b)
    have heq :
        (a * c / b) * ((1 + (b * log (x / c)) ^ 2)⁻¹ * (b * x⁻¹)) = g' x := by
      simp only [g']
      field_simp [inv_eq_one_div, hb.ne', hc.ne', hx.ne']
    simpa [g, heq] using hder
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [_root_.dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  refine (cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ l3
  simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  have hsum_ico :
      (∑ x_1 ∈ Finset.Ico 1 n,
          if x_1 = 0 then 1 else x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x)) =
        ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : i ≠ 0 := by omega
    simp [this]
  rw [hsum_ico]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa [one_div, mul_inv_rev] using (this.mono_set Ioi_subset_Ici_self).integrable

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  calc
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖
        = ‖f i / i‖ * ‖𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ := by
          rw [norm_mul]
    _ ≤ ‖f i / i‖ * (W21.norm ψ * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
            (norm_nonneg (f i / i))
    _ = W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
          simp only [Complex.norm_div, RCLike.norm_natCast]
          ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  calc
    (∑' (i : ℕ), ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖)
        ≤ ∑' (i : ℕ),
            W21.norm ψ * (‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹) :=
          Summable.tsum_mono l1 (by simpa [smul_eq_mul] using l5.const_smul (W21.norm ψ)) l6
    _ = W21.norm ψ *
          ∑' (i : ℕ), ‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹ := by
          simpa [smul_eq_mul] using Summable.tsum_const_smul (W21.norm ψ) l5

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring

set_option backward.isDefEq.respectTransparency false in
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [_root_.dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    change ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ < ε / 2
    have : 0 < 1 + M := by positivity
    have hbound :
        ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ ≤
          W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun * M := by
      simpa [S, S1, S2, M] using @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply hbound.trans_lt
    have hnorm :
        W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun = W21.norm (ψ.toFun - (Ψ R).toFun) := by
      simp [W21.ofCS2]
    rw [hnorm]
    have hMle : M ≤ 1 + M := by linarith
    apply (mul_le_mul_of_nonneg_left hMle W21.norm_nonneg).trans_lt
    calc
      W21.norm (ψ.toFun - (Ψ R).toFun) * (1 + M)
          < (ε / 2 / (1 + M)) * (1 + M) := mul_lt_mul_of_pos_right hRψ this
      _ = ε / 2 := by field_simp [this.ne']

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'

-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f

noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

set_option backward.isDefEq.respectTransparency false in
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, _root_.dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]

lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    have hprod : HasCompactSupport
        (((fun x : ℝ => cexp (2 * ↑π * ↑x)) * fun x => Ψ (rexp (2 * π * x)))) :=
      (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
    rw [hasCompactSupport_iff_eventuallyEq] at hprod ⊢
    exact hprod.mono fun x hx => by
      simpa [h, Pi.mul_apply] using hx
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4

lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

@[norm_cast]
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, _root_.dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, _root_.dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume (Function.support ψ ∩ Ioi 0) := by
      calc
        (1 : ENNReal) = volume (Ico (1 : ℝ) 2) := by
          simp [Real.volume_Ico]
          norm_num
        _ ≤ volume (Function.support ψ ∩ Ioi 0) := volume.mono r4
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this

lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`

/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [_root_.dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    rw [Finset.range_eq_Ico] ; symm ; rw [Finset.range_eq_Ico]
    exact Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
      (Nat.ceil_le.mpr (mul_le_of_le_one_left N.cast_nonneg hε))
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [Real.dist_eq, ← S_sub_S h2.2] using l2.trans_lt h1

set_option maxHeartbeats 1000000 in
-- The Wiener-Ikehara argument below combines several long asymptotic estimates,
-- and the final proof search exceeds Lean's default heartbeat limit.
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  have h_event : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Tendsto (S f ε) atTop (𝓝 (A * (1 - ε))) := by
    have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    intro ε hε
    have hdisc := WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
    exact hdisc.congr' (Eventually.of_forall fun N => by simp [S])
  have hlim : Tendsto (fun ε : ℝ => A * (1 - ε)) (𝓝[>] 0) (𝓝 A) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (hε.const_sub 1).const_mul A
  have hmain : Tendsto (S f 0) atTop (𝓝 A) :=
    (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto h_event hlim
  exact hmain.congr' (Eventually.of_forall fun N => by simp [S, cumsum])

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_ofPred_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

section auto_cheby

variable {f : ℕ → ℝ}

lemma norm_x_cpow_it (x t : ℝ) (hx : 0 < x) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
  rw [cpow_def_of_ne_zero <| ofReal_ne_zero.mpr hx.ne', ← ofReal_log hx.le]
  convert norm_exp_ofReal_mul_I (t * x.log) using 2
  push_cast; ring_nf

set_option backward.isDefEq.respectTransparency false in
lemma limiting_fourier_aux_gt_zero (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 0 < x) (σ' : ℝ) (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) :=
    (((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8).integrable_of_hasCompactSupport
      ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := fun h ↦ by
    have := congrArg Complex.re (sub_eq_zero.mp h); simp at this; linarith
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) *
      (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    have : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) *
        (↑(x ^ (σ' - 1)) * (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
      simp only [one_div, ← mul_assoc]
      exact ((continuous_const.mul (Continuous.inv₀ (by fun_prop) e2)).mul ψ.h1.continuous).mul l8
    exact this.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [first_fourier hf hint hx hσ', second_fourier ψ.h1.continuous.measurable hint hx hσ',
    ← integral_const_mul, ← integral_sub l4 l5]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  field_simp [e2]; norm_cast; simp [mul_assoc, ← rpow_add hx]

theorem limiting_fourier_lim2_gt_zero (A : ℝ) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
      ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
        (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  refine Tendsto.mul ?_ (tendsto_integral_filter_of_dominated_convergence _
    (.of_forall fun _ ↦ (by continuity : Continuous _).aestronglyMeasurable) ?_
    (limiting_fourier_lim2_aux x C) (.of_forall fun u ↦ ?_))
  · suffices Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) by
      simpa using ((continuous_ofReal.tendsto 1).comp this).const_mul ↑A
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using (continuous_id.tendsto (1 : ℝ)).const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl hx.ne')
  · refine eventually_of_mem (Ioo_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun σ' hσ' ↦ ?_
    obtain ⟨h1, h2⟩ := hσ'
    rw [ae_restrict_iff' measurableSet_Ici]
    refine .of_forall fun t ht ↦ ?_
    simp only [norm_mul, neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one,
      norm_exp, neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im,
      sub_self, mul_zero, sub_zero]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) ((abs_nonneg x).trans (le_max_left _ _))
    have hα0 : 0 ≤ σ' - 1 := by linarith
    have hα1 : σ' - 1 ≤ 1 := by linarith
    have hmul1 : (-x.log) * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht hα0
    calc Real.exp (-(t * (σ' - 1)))
        ≤ Real.exp (x.log * (σ' - 1)) := Real.exp_monotone (by linarith)
      _ ≤ max |x| 1 := by
          by_cases hx1 : 1 ≤ x
          · calc _ ≤ Real.exp x.log :=
                Real.exp_monotone (mul_le_of_le_one_right (Real.log_nonneg hx1) hα1)
              _ = |x| := by rw [Real.exp_log hx, abs_of_pos hx]
              _ ≤ _ := le_max_left _ _
          · calc _ ≤ 1 := (Real.exp_monotone (mul_nonpos_of_nonpos_of_nonneg
                  ((Real.log_neg_iff hx).2 (by linarith)).le hα0)).trans_eq Real.exp_zero
              _ ≤ _ := le_max_right _ _
  · suffices Tendsto (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by simpa using this.mul_const _
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    have : Continuous (fun n ↦ ((rexp (-u * (n - 1))) : ℂ)) := by continuity
    simpa using this.tendsto 1

theorem limiting_fourier_lim3_gt_zero
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_Icc.reProdIm (isClosed_tsupport ψ), (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded⟩
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩ (hG.mono l2).norm
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun a ↦ ‖G z‖ * ‖ψ a‖)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      ((hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous).mul
        (by simpa using Continuous.const_cpow (by fun_prop) (Or.inl hxC)) |>.aestronglyMeasurable)
    (eventually_of_mem (Icc_mem_nhdsGT_of_mem (by norm_num : (1 : ℝ) ∈ Set.Ico 1 2)) fun u hu ↦
      .of_forall fun v ↦ ?_)
    ((continuous_const.mul ψ.h1.continuous.norm).integrable_of_hasCompactSupport ψ.h2.norm.mul_left)
    (.of_forall fun t ↦ ?_)
  · by_cases h : v ∈ tsupport ψ
    · simp_rw [norm_mul, norm_x_cpow_it x v hx, mul_one]
      exact mul_le_mul_of_nonneg_right (isMaxOn_iff.mp hmax _ (by simp [S, mem_reProdIm, hu.1, hu.2, h])) (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp [Function.notMem_support.mp this]
  · exact ((hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr
      ⟨((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds,
       eventually_nhdsWithin_of_forall fun _ hx' ↦ by simp [(Set.mem_Ioi.mp hx').le]⟩).mul_const _ |>.mul_const _

lemma tendsto_tsum_of_monotone_convergence
    {β : Type*} {f : ℕ → β → ENNReal} {g : β → ENNReal}
    (hmono : ∀ k, Monotone (fun n => f n k))
    (hlim : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (g k))) :
    Tendsto (fun n => ∑' k, f n k) atTop (𝓝 (∑' k, g k)) := by
  let : MeasurableSpace β := ⊤
  let μ : Measure β := Measure.count
  have hg_iSup (k : β) : (⨆ n : ℕ, f n k) = g k := iSup_eq_of_tendsto (hmono k) (hlim k)
  have h_tend_lint : Tendsto (fun n => ∫⁻ k, f n k ∂μ) atTop (𝓝 (∫⁻ k, (⨆ n, f n k) ∂μ)) := by
    have hmeas : ∀ n, Measurable fun k : β => f n k := fun _ _ _ ↦ trivial
    have hmono_fn : Monotone (fun n => fun k : β => f n k) := fun _ _ hnm k ↦ hmono k hnm
    simpa [lintegral_iSup hmeas hmono_fn] using
      tendsto_atTop_iSup fun _ _ hmn ↦ lintegral_mono fun k ↦ hmono k hmn
  simpa [μ, lintegral_count, hg_iSup] using h_tend_lint

lemma tendsto_tsum_of_monotone_convergence_nhdsGT_one
    {F : ℝ → ℕ → ℝ}
    (hF_nonneg : ∀ σ n, 0 ≤ F σ n)
    (hF_antitone : ∀ n, AntitoneOn (fun σ : ℝ => F σ n) (Set.Ioi (1 : ℝ)))
    (hF_tend : ∀ n, Tendsto (fun σ : ℝ => F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (F 1 n)))
    (hSumm : ∀ σ, 1 < σ → Summable (fun n : ℕ => F σ n))
    (hbounded :
      BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => (∑' n : ℕ, F σ n))) :
    Tendsto (fun σ : ℝ => ∑' n : ℕ, F σ n) (𝓝[>] (1 : ℝ)) (𝓝 (∑' n : ℕ, F 1 n)) := by
  let T : ℝ → ℝ := fun σ => ∑' n : ℕ, F σ n
  have hT_antitone : AntitoneOn T (Set.Ioi (1 : ℝ)) := fun a ha b hb hab ↦
    (hSumm b hb).tsum_le_tsum_of_inj (fun n ↦ n) (fun _ _ h ↦ h) (fun c hc ↦ (hc ⟨c, rfl⟩).elim)
      (fun n ↦ hF_antitone n ha hb hab) (hSumm a ha)
  have hT_bdd : BddAbove (T '' Set.Ioi (1 : ℝ)) := by
    obtain ⟨C, hC⟩ := isBigO_iff.1 hbounded
    have hC' : ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ), T σ ≤ C := by
      filter_upwards [hC] with σ hσ
      calc T σ ≤ |T σ| := le_abs_self _
        _ = ‖T σ‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖(1 : ℝ → ℝ) σ‖ := hσ
        _ = C := by simp
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_inf_iff_superset.1 hC'
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    have hIoi_sub : Set.Ioi (1 : ℝ) ⊆ V := Filter.mem_principal.mp hV
    have hUsub : U ∩ Set.Ioi (1 : ℝ) ⊆ {σ : ℝ | T σ ≤ C} := fun σ hσ ↦ hUV ⟨hσ.1, hIoi_sub hσ.2⟩
    have hσ0_Ioi : 1 + ε / 2 ∈ Set.Ioi (1 : ℝ) := by simp [half_pos hε]
    have hσ0_leC : T (1 + ε / 2) ≤ C :=
      hUsub ⟨hball (by simp only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos (half_pos hε)]; exact half_lt_self hε), hσ0_Ioi⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨σ, hσIoi, rfl⟩
    by_cases hσlt : σ < 1 + ε / 2
    · exact hUsub ⟨hball (by
        simp only [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_pos (sub_pos.2 (Set.mem_Ioi.mp hσIoi))]
        linarith [half_lt_self hε]), hσIoi⟩
    · exact (hT_antitone hσ0_Ioi hσIoi (le_of_not_gt hσlt)).trans hσ0_leC
  have hT_tend_sup : Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (sSup (T '' Set.Ioi (1 : ℝ)))) :=
    hT_antitone.tendsto_nhdsGT hT_bdd
  let σseq : ℕ → ℝ := fun k => 1 + 1 / (k + 1 : ℝ)
  have hσseq_mem (k) : σseq k ∈ Set.Ioi (1 : ℝ) := by
    simp only [σseq, Set.mem_Ioi, lt_add_iff_pos_right]
    positivity
  have hσseq_tend_nhds : Tendsto σseq atTop (𝓝 (1 : ℝ)) := by
    have : Tendsto (fun k : ℕ => (1 : ℝ) + ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 ((1 : ℝ) + 0)) :=
      tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1))
    simp only [add_zero] at this
    convert this using 1; ext k; simp [σseq, one_div]
  have hσseq_tend_nhdsWithin : Tendsto σseq atTop (𝓝[>] (1 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσseq_tend_nhds
      (.of_forall hσseq_mem)
  have hσseq_antitone : Antitone σseq := fun k₁ k₂ hk ↦ by simp only [σseq]; gcongr
  have hmono_seq (n) : Monotone (fun k => F (σseq k) n) := fun k₁ k₂ hk ↦
    hF_antitone n (hσseq_mem k₂) (hσseq_mem k₁) (hσseq_antitone hk)
  have htend_seq (n) : Tendsto (fun k => F (σseq k) n) atTop (𝓝 (F 1 n)) :=
    (hF_tend n).comp hσseq_tend_nhdsWithin
  have hTseq : Tendsto (fun k : ℕ => T (σseq k)) atTop (𝓝 (T 1)) := by
    have hsum1 : Summable (fun n : ℕ => F (1 : ℝ) n) := by
      obtain ⟨C, hC⟩ := hT_bdd
      refine summable_of_sum_range_le (hF_nonneg 1) fun m ↦ le_of_tendsto
        (tendsto_finsetSum _ fun i _ ↦ hF_tend i)
        (eventually_of_mem self_mem_nhdsWithin fun σ hσ ↦
          ((hSumm σ hσ).sum_le_tsum _ (fun n _ ↦ hF_nonneg σ n)).trans (hC ⟨σ, hσ, rfl⟩))
    have hg_ne_top : (∑' n : ℕ, ENNReal.ofReal (F 1 n)) ≠ ⊤ := hsum1.tsum_ofReal_ne_top
    have hENN : Tendsto (fun k => ∑' n, ENNReal.ofReal (F (σseq k) n)) atTop
        (𝓝 (∑' n, ENNReal.ofReal (F 1 n))) :=
      tendsto_tsum_of_monotone_convergence (fun n _ _ hk ↦ ENNReal.ofReal_le_ofReal (hmono_seq n hk))
        (fun n ↦ ENNReal.tendsto_ofReal (htend_seq n))
    have hrew (σ) : (∑' n, ENNReal.ofReal (F σ n)).toReal = ∑' n, F σ n := by
      rw [ENNReal.tsum_toReal_eq (fun n ↦ by simp)]
      exact tsum_congr fun n ↦ by simp [hF_nonneg σ n]
    simp only [T, ← hrew]; exact (ENNReal.tendsto_toReal hg_ne_top).comp hENN
  have hsSup_eq : sSup (T '' Set.Ioi (1 : ℝ)) = T 1 :=
    tendsto_nhds_unique (hT_tend_sup.comp hσseq_tend_nhdsWithin) hTseq
  simpa [T, hsSup_eq] using hT_tend_sup

lemma limiting_fourier_variant_lim1_aux
    {f : ℕ → ℝ} {x : ℝ} (ψ : CS 2 ℂ)
    (hpos : 0 ≤ f)
    (hf : ∀ (σ : ℝ), 1 < σ → Summable (nterm f σ))
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∀ (σ : ℝ), 1 < σ →
      Summable (fun n : ℕ =>
        (if n = 0 then 0 else f n / ((n : ℝ) ^ σ)) *
          (𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))).re) := by
  intro σ hσ
  let y : ℕ → ℝ := fun n => (1 / (2 * π)) * Real.log ((n : ℝ) / x)
  let W : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re
  let base : ℕ → ℝ := fun n => if n = 0 then 0 else f n / ((n : ℝ) ^ σ)
  obtain ⟨C, hC⟩ := decay_bounds_cor (W21.ofCS2 ψ)
  have hC_nonneg : 0 ≤ C := (norm_nonneg _).trans ((hC 0).trans (by simp))
  have hW_nonneg (n : ℕ) : 0 ≤ W n := (hψpos (y n)).1
  have hnorm_four (n : ℕ) : ‖𝓕 ψ.toFun (y n)‖ = W n := by
    have him0 : (𝓕 ψ.toFun (y n)).im = 0 := (hψpos (y n)).2
    rw [show 𝓕 ψ.toFun (y n) = W n by exact Complex.ext rfl him0]
    simp [abs_of_nonneg (hW_nonneg n)]
  have hW_le_C (n : ℕ) : W n ≤ C := by
    rw [← hnorm_four]; exact (hC (y n)).trans (div_le_self hC_nonneg (by nlinarith [sq_nonneg (y n)]))
  have hbase_summ : Summable base := by
    convert hf σ hσ using 1; ext n
    by_cases hn : n = 0 <;> simp [nterm, base, hn, Real.norm_eq_abs, abs_of_nonneg (hpos n)]
  refine (hbase_summ.mul_left C).of_norm_bounded fun n ↦ ?_
  by_cases hn : n = 0
  · simp [base, hn]
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase_nonneg : 0 ≤ base n := by
      simp only [base, hn, if_false]
      exact div_nonneg (hpos n) (Real.rpow_pos_of_pos hnpos σ).le
    calc |base n * W n| = base n * W n := abs_of_nonneg (mul_nonneg hbase_nonneg (hW_nonneg n))
      _ ≤ base n * C := mul_le_mul_of_nonneg_left (hW_le_C n) hbase_nonneg
      _ = C * base n := mul_comm _ _

theorem limiting_fourier_variant_lim1
    {f : ℕ → ℝ} {x : ℝ} {ψ : CS 2 ℂ}
    (hpos : 0 ≤ f)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (S : ℝ → ℂ)
    (hSdef :
      ∀ σ' : ℝ,
        S σ' =
          ∑' n : ℕ,
            term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
              𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
    (hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖))
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) :
    Tendsto
      (fun σ' : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ' : ℝ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑' n : ℕ,
          (f n : ℂ) / (n : ℂ) *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x)))) := by

  let y : ℕ → ℝ := fun n => (π⁻¹ * 2⁻¹) * Real.log ((n : ℝ) / x)
  let w : ℕ → ℝ := fun n => (𝓕 ψ.toFun (y n)).re

  have hw_nonneg : ∀ n, 0 ≤ w n := by
    intro n
    exact (hψpos (y n)).1

  have hFour_eq_ofReal : ∀ n, 𝓕 ψ.toFun (y n) = Complex.ofReal (w n) := by
    intro n
    have h := hψpos (y n)
    refine Complex.ext ?_ ?_
    · simp [w]
    · simp [w, h.2]

  let rterm : ℝ → ℕ → ℝ :=
    fun σ n =>
      if h0 : n = 0 then 0 else (f n) / ((n : ℝ) ^ σ) * (w n)

  have summand_eq_ofReal :
      ∀ (σ : ℝ) (n : ℕ),
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
          = Complex.ofReal (rterm σ n) := by
    intro σ n
    by_cases hn : n = 0
    · subst hn
      simp [rterm, y]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn0 : 0 ≤ (n : ℝ) := le_of_lt hnpos
      have hcpow :
          ( (n : ℂ) ^ ((σ : ℝ) : ℂ) ) = ( ( (n : ℝ) ^ σ : ℝ) : ℂ ) := by
        simpa using (Complex.ofReal_cpow hn0 σ).symm
      have hpow_ne : ((n : ℝ) ^ σ) ≠ 0 := by
        exact (ne_of_gt (Real.rpow_pos_of_pos hnpos σ))
      calc
        term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)
            =
          ((f n : ℂ) / ((n : ℂ) ^ ((σ : ℝ) : ℂ))) * ( (w n : ℝ) : ℂ ) := by
            simp [term, LSeries.term, hn, hFour_eq_ofReal]
        _ =
          ((f n : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp [hcpow]
        _ =
          (( (f n : ℝ) : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)) * ((w n : ℝ) : ℂ) := by
            simp
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) : ℝ) : ℂ ) * ((w n : ℝ) : ℂ) := by
            simp [Complex.ofReal_div]
        _ =
          ( ( (f n : ℝ) / ((n : ℝ) ^ σ) * (w n) : ℝ ) : ℂ ) := by
            simp [Complex.ofReal_mul]
        _ =
          Complex.ofReal (rterm σ n) := by
            simp [rterm, hn]

  let T : ℝ → ℝ := fun σ => ∑' n, rterm σ n

  have tsum_eq_ofReal_T : ∀ σ : ℝ,
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = Complex.ofReal (T σ) := by
    intro σ
    have hcongr :
        (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := by
      refine tsum_congr ?_
      intro n
      simpa using (summand_eq_ofReal σ n)

    calc
      (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          = ∑' n : ℕ, (Complex.ofReal (rterm σ n)) := hcongr
      _ = Complex.ofReal (∑' n : ℕ, rterm σ n) := by
            simpa using (Complex.ofReal_tsum (fun n : ℕ => rterm σ n)).symm
      _ = Complex.ofReal (T σ) := by rfl

  have hS_ofReal_T : ∀ σ : ℝ, S σ = Complex.ofReal (T σ) := by
    intro σ
    simpa [hSdef σ, y] using (tsum_eq_ofReal_T σ)

  have rterm_nonneg : ∀ σ n, 0 ≤ rterm σ n := by
    intro σ n
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hden : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
      have : 0 ≤ (f n) / ((n : ℝ) ^ σ) := div_nonneg hf (le_of_lt hden)
      simp [rterm, hn, mul_nonneg this hw]

  have T_nonneg : ∀ σ, 0 ≤ T σ := by
    intro σ
    exact tsum_nonneg (fun n => rterm_nonneg σ n)

  have hT_eq_normS : ∀ σ, T σ = ‖S σ‖ := by
    intro σ
    have := hS_ofReal_T σ
    calc
      T σ = ‖Complex.ofReal (T σ)‖ := by simp [abs_of_nonneg (T_nonneg σ)]
      _ = ‖S σ‖ := by simp [this]

  have hboundedT : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ : ℝ => T σ) := by
    have : (fun σ : ℝ => T σ) = (fun σ : ℝ => ‖S σ‖) := by
      funext σ; exact hT_eq_normS σ
    simpa [this] using hbounded

  have rterm_antitone : ∀ n, AntitoneOn (fun σ => rterm σ n) (Set.Ioi 1) := by
    intro n σ₁ hσ₁ σ₂ hσ₂ hσ₁₂
    by_cases hn : n = 0
    · subst hn; simp [rterm]
    · have hf : 0 ≤ f n := hpos n
      have hw : 0 ≤ w n := hw_nonneg n
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hpow : (n : ℝ) ^ σ₁ ≤ (n : ℝ) ^ σ₂ :=
        Real.rpow_le_rpow_of_exponent_le hn1 hσ₁₂
      have hinv :
      (1 / ((n : ℝ) ^ σ₂)) ≤ (1 / ((n : ℝ) ^ σ₁)) := by
        have hpos1 : 0 < (n : ℝ) ^ σ₁ := Real.rpow_pos_of_pos hnpos σ₁
        exact one_div_le_one_div_of_le hpos1 hpow
      have hinv_inv : ((n : ℝ) ^ σ₂)⁻¹ ≤ ((n : ℝ) ^ σ₁)⁻¹ := by
        simpa [one_div] using hinv
      have hmul1 :
          (f n) * (((n : ℝ) ^ σ₂)⁻¹) ≤ (f n) * (((n : ℝ) ^ σ₁)⁻¹) :=
        mul_le_mul_of_nonneg_left hinv_inv hf
      have hmul2 :
          ((f n) * (((n : ℝ) ^ σ₂)⁻¹)) * (w n)
            ≤ ((f n) * (((n : ℝ) ^ σ₁)⁻¹)) * (w n) :=
        mul_le_mul_of_nonneg_right hmul1 hw
      simpa [rterm, hn, div_eq_mul_inv, mul_assoc] using hmul2

  have rterm_tend : ∀ n, Tendsto (fun σ : ℝ => rterm σ n) (𝓝[>] (1 : ℝ)) (𝓝 (rterm 1 n)) := by
    intro n
    have hterm :
        Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
          (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
      by_cases hn : n = 0
      · subst hn
        simp [term, LSeries.term]
      · have hden :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 ((n : ℂ) ^ (1 : ℂ))) := by
          simpa using ((continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).const_cpow

        have hden' :
            Tendsto (fun σ : ℝ => ((n : ℂ) ^ ((σ : ℝ) : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 (n : ℂ)) := by
          simpa using hden

        have hnC : (n : ℂ) ≠ 0 := by
          exact_mod_cast hn

        have hterm :
            Tendsto (fun σ : ℝ => term (fun n ↦ (f n : ℂ)) (σ : ℝ) n)
              (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ))) := by
          have hnC : (n : ℂ) ≠ 0 := by
            exact_mod_cast hn
          simp only [term, LSeries.term, hn, ↓reduceIte]
          change Tendsto (((fun _ : ℝ => (f n : ℂ)) /
              fun σ : ℝ => (n : ℂ) ^ ((σ : ℝ) : ℂ)))
            (𝓝[>] (1 : ℝ)) (𝓝 ((f n : ℂ) / (n : ℂ)))
          exact tendsto_const_nhds.div hden' hnC
        exact hterm

    have hsummand :
        Tendsto
          (fun σ : ℝ =>
            term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
          (𝓝[>] (1 : ℝ))
          (𝓝 (((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n))) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (hterm.mul_const (𝓕 ψ.toFun (y n)))

    have hre : ∀ σ, rterm σ n =
        (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re := by
      intro σ
      have := congrArg Complex.re (summand_eq_ofReal σ n)
      simpa [Complex.ofReal_re] using this.symm

    have hRe : Tendsto
        (fun σ : ℝ =>
          (term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n)).re)
        (𝓝[>] (1 : ℝ))
        (𝓝 ((((f n : ℂ) / (n : ℂ)) * 𝓕 ψ.toFun (y n)).re)) :=
      (continuous_re.tendsto _).comp hsummand

    have hlimit_re :
      (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re = rterm 1 n := by
      have h0 :
          (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re = rterm 1 n := by
        have := congrArg Complex.re (summand_eq_ofReal (σ := (1 : ℝ)) n)
        simpa [Complex.ofReal_re] using this

      by_cases hn : n = 0
      · subst hn
        simp [rterm, y]
      · have h1 :
            (term (fun n ↦ (f n : ℂ)) (1 : ℝ) n * 𝓕 ψ.toFun (y n)).re
              = (f n / (n : ℝ)) * (𝓕 ψ.toFun (y n)).re := by
          simp [Complex.mul_re, term, LSeries.term, hn, y,
                (hψpos (y n)).2]

        exact (h1.symm.trans h0)

    simpa [hre, hlimit_re] using hRe

  have hSumm_rterm : ∀ σ : ℝ, 1 < σ → Summable (fun n : ℕ => rterm σ n) := by
    simpa [rterm] using limiting_fourier_variant_lim1_aux (ψ := ψ)
      (f := f) (x := x) hpos hf hψpos

  have hT_tend :
      Tendsto T (𝓝[>] (1 : ℝ)) (𝓝 (T 1)) := by
    have :
        Tendsto (fun σ : ℝ => ∑' n : ℕ, rterm σ n)
          (𝓝[>] (1 : ℝ))
          (𝓝 (∑' n : ℕ, rterm (1 : ℝ) n)) := by
      refine tendsto_tsum_of_monotone_convergence_nhdsGT_one
        (F := rterm)
        (hF_nonneg := rterm_nonneg)
        (hF_antitone := rterm_antitone)
        (hF_tend := rterm_tend)
        (hSumm := hSumm_rterm)
        (hbounded := hboundedT)

    simpa [T] using this

  have hToReal :
      Tendsto (fun σ => Complex.ofReal (T σ)) (𝓝[>] (1 : ℝ)) (𝓝 (Complex.ofReal (T 1))) :=
    (continuous_ofReal.tendsto _).comp hT_tend

  have hsource :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          term (fun n ↦ (f n : ℂ)) (σ : ℝ) n * 𝓕 ψ.toFun (y n))
        = fun σ : ℝ => Complex.ofReal (T σ) := by
    funext σ
    exact (tsum_eq_ofReal_T σ)

  have hσ1 :
    (∑' n : ℕ, term (fun n ↦ (f n : ℂ)) (↑(1:ℝ)) n * 𝓕 ψ.toFun (y n))
      = (↑(T 1) : ℂ) :=
    by simpa using (tsum_eq_ofReal_T (σ := (1:ℝ)))
  have hterm1 :
      ∀ n : ℕ, term (fun n ↦ (f n : ℂ)) (1 : ℂ) n = (f n : ℂ) / (n : ℂ) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [term, LSeries.term]
    · simp [term, LSeries.term, hn]

  have hrewrite :
      (∑' n : ℕ,
        term (fun n ↦ (f n : ℂ)) (1 : ℂ) n * 𝓕 ψ.toFun (y n))
        =
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n)) := by
    refine tsum_congr ?_
    intro n
    simp [hterm1 n]

  have htarget :
      (∑' n : ℕ,
        (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (y n))
        = (↑(T 1) : ℂ) := by
    exact (hrewrite.symm.trans hσ1)

  simpa [hsource, htarget, y] using hToReal

lemma limiting_fourier_variant
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0)
    (hx : 0 < x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l2 := limiting_fourier_lim2_gt_zero (A := A) (x := x) ψ hx
  have l3 := limiting_fourier_lim3_gt_zero (G := G) (x := x) hG ψ hx

  let S : ℝ → ℂ := fun σ' =>
    ∑' n : ℕ,
      term (fun n ↦ (f n : ℂ)) σ' n *
        𝓕 ψ.toFun (1 / (2 * π) * Real.log ((n : ℝ) / x))
  let Pole : ℝ → ℂ := fun σ' =>
    (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
      ∫ u in Set.Ici (-Real.log x),
        (rexp (-u * (σ' - 1)) : ℂ) *
          𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' =>
    ∫ t : ℝ, G (σ' + t * I) * ψ.toFun t * (x : ℂ) ^ (t * I)

  have haux :
    (fun σ' ↦
        ∑' (n : ℕ),
          term (fun n ↦ (f n : ℂ)) (σ' : ℂ) n *
            𝓕 ψ.toFun (π⁻¹ * 2⁻¹ * Real.log ((n : ℝ) / x))
        - (A : ℂ) * ((x ^ (1 - σ') : ℝ) : ℂ) *
          ∫ (u : ℝ) in Ici (-Real.log x),
            cexp (-( (u : ℂ) * ((σ' : ℂ) - 1))) *
              𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π)))
      =ᶠ[𝓝[>] (1 : ℝ)]
    (fun σ' ↦
      ∫ (t : ℝ), G ((σ' : ℂ) + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)) := by
    rw [Filter.EventuallyEq]

    refine eventually_nhdsWithin_of_forall ?_
    intro σ' hσ'
    have hσ' : (1 : ℝ) < σ' := by
      simpa [Set.mem_Ioi] using hσ'
    simpa using (limiting_fourier_aux_gt_zero (G := G) (f := f) (A := A) hG' hf ψ hx σ' hσ')

  have haux' :
    (fun σ' : ℝ => S σ') =ᶠ[𝓝[>] (1 : ℝ)] (fun σ' : ℝ => RHS σ' + Pole σ') := by
    rw [Filter.EventuallyEq] at haux ⊢
    filter_upwards [haux] with σ' hσ'
    have hσ'' : S σ' - Pole σ' = RHS σ' := by
      simpa [S, Pole, RHS] using hσ'
    have hadd : (S σ' - Pole σ') + Pole σ' = RHS σ' + Pole σ' :=
      congrArg (fun z : ℂ => z + Pole σ') hσ''
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

  let Pole₁ : ℂ := (A : ℂ) * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψ).toFun (u / (2 * π))
  let RHS₁ : ℂ := ∫ t : ℝ, G (1 + (t : ℂ) * I) * ψ.toFun t * (x : ℂ) ^ ((t : ℂ) * I)

  have hRHS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖RHS σ'‖ ≤ ‖RHS₁‖ + 1 := by
    have hball : Metric.ball RHS₁ (1 : ℝ) ∈ 𝓝 RHS₁ := by
      simpa using (Metric.ball_mem_nhds (x := RHS₁) (ε := (1 : ℝ)) (by norm_num))
    have hpre : {σ' : ℝ | RHS σ' ∈ Metric.ball RHS₁ (1 : ℝ)} ∈ (𝓝[>] (1 : ℝ)) :=
      l3 hball
    filter_upwards [hpre] with σ' hmem
    have hdist' : dist (RHS σ') RHS₁ < (1 : ℝ) := by
      simpa [Metric.mem_ball] using hmem
    have hdist : ‖RHS σ' - RHS₁‖ < (1 : ℝ) := by
      simpa [dist_eq_norm] using hdist'
    have htri : ‖RHS σ'‖ ≤ ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ := by
      have h := norm_add_le (RHS σ' - RHS₁) RHS₁
      simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using h
    have hle : ‖RHS₁‖ + ‖RHS σ' - RHS₁‖ ≤ ‖RHS₁‖ + (1 : ℝ) := by
      exact add_le_add_right (le_of_lt hdist) ‖RHS₁‖
    exact htri.trans hle

  have hPole_le :
    ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ), ‖Pole σ'‖ ≤ ‖Pole₁‖ + 1 := by
    have hball : Metric.ball Pole₁ 1 ∈ 𝓝 Pole₁ := by
      simpa using (Metric.ball_mem_nhds Pole₁ (by norm_num : (0 : ℝ) < 1))
    have hpre : {σ' : ℝ | Pole σ' ∈ Metric.ball Pole₁ 1} ∈ (𝓝[>] (1 : ℝ)) := l2 hball
    filter_upwards [hpre] with σ' hmem
    have hdist : ‖Pole σ' - Pole₁‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hmem
    have htri : ‖Pole σ'‖ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := by
      have hdecomp : Pole σ' = Pole₁ + (Pole σ' - Pole₁) := by abel
      have hnorm_eq : ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := by
        simp [congrArg (fun z : ℂ => ‖z‖) hdecomp]
      calc
        ‖Pole σ'‖ = ‖Pole₁ + (Pole σ' - Pole₁)‖ := hnorm_eq
        _ ≤ ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ := norm_add_le _ _
    have hdist_le : ‖Pole σ' - Pole₁‖ ≤ 1 := le_of_lt hdist
    have hsum : ‖Pole₁‖ + ‖Pole σ' - Pole₁‖ ≤ ‖Pole₁‖ + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hdist_le ‖Pole₁‖)
    exact htri.trans hsum

  have hS_le :
      ∀ᶠ σ' : ℝ in 𝓝[>] (1 : ℝ),
        ‖S σ'‖ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
    rw [Filter.EventuallyEq] at haux'
    filter_upwards [haux', hRHS_le, hPole_le] with σ' hEq hR hP
    calc
      ‖S σ'‖ = ‖RHS σ' + Pole σ'‖ := by simp [hEq]
      _ ≤ ‖RHS σ'‖ + ‖Pole σ'‖ := norm_add_le _ _
      _ ≤ (‖RHS₁‖ + 1) + (‖Pole₁‖ + 1) := by
        exact add_le_add hR hP

  have hbounded : BoundedAtFilter (𝓝[>] (1 : ℝ)) (fun σ' : ℝ => ‖S σ'‖) := by
    let C : ℝ := ‖RHS₁‖ + 1 + (‖Pole₁‖ + 1)
    simp only [BoundedAtFilter, Asymptotics.IsBigO, Asymptotics.IsBigOWith]
    refine ⟨C, ?_⟩
    filter_upwards [hS_le] with σ' hσ'
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (S σ'))] using hσ'

  have hcoef : (1 / (2 * π) : ℝ) = (π⁻¹ * 2⁻¹ : ℝ) := by field_simp [pi_ne_zero]

  have l1 :=
    limiting_fourier_variant_lim1
      (f := f) (x := x) (ψ := ψ)
      hpos hψpos
      (S := S)
      (hSdef := by
        intro σ
        simp [S, hcoef] )
      hbounded
      hf
  have l1S :
    Tendsto S (𝓝[>] (1 : ℝ))
      (𝓝 (∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x)))) := by
    simpa [S, hcoef] using l1

  have l12 : Tendsto (fun σ' : ℝ => S σ' - Pole σ') (𝓝[>] (1 : ℝ))
    (𝓝 ((∑' n : ℕ, (f n : ℂ) / (n : ℂ) * 𝓕 ψ.toFun (1 / (2 * π) * Real.log (↑n / x))) - Pole₁)) :=
  l1S.sub l2

  have hPole : (Pole : ℝ → ℂ) =ᶠ[𝓝[>] (1 : ℝ)] Pole := by simp
  have haux_sub :
    (fun σ' : ℝ => S σ' - Pole σ') =ᶠ[𝓝[>] (1 : ℝ)] RHS := by
    filter_upwards [haux'] with σ' hσ'
    calc
      S σ' - Pole σ'
          = (RHS σ' + Pole σ') - Pole σ' := by simp [hσ']
      _   = RHS σ' := by simp
  have hlim :=
    tendsto_nhds_unique_of_eventuallyEq (l1S.sub l2) l3 haux_sub

  simpa [Pole₁, RHS₁] using hlim

lemma norm_mul_integral_Ici_le_integral_norm
    (A : ℂ) (F : ℝ → ℂ) (a : ℝ)
    (hF : IntegrableOn F (Set.Ici a))
    (hnorm : Integrable (fun u : ℝ => ‖F u‖)) :
    ‖A * (∫ u in Set.Ici a, F u)‖ ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) := by
  have hmul : ‖A * (∫ u in Set.Ici a, F u)‖ = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := by
    simp
  have hnormI :
      ‖∫ u in Set.Ici a, F u‖ ≤ ∫ u in Set.Ici a, ‖F u‖ := by
    have _ : Integrable F (Measure.restrict volume (Set.Ici a)) := hF
    have h :
        ‖∫ u, F u ∂Measure.restrict volume (Set.Ici a)‖
          ≤ ∫ u, ‖F u‖ ∂Measure.restrict volume (Set.Ici a) :=
      norm_integral_le_integral_norm (μ := Measure.restrict volume (Set.Ici a)) (f := F)
    simpa using h

  have hdom :
      (∫ u in Set.Ici a, ‖F u‖) ≤ ∫ u : ℝ, ‖F u‖ := by
    have hEq :
        (∫ u in Set.Ici a, ‖F u‖) =
          ∫ u : ℝ, Set.indicator (Set.Ici a) (fun u => ‖F u‖) u := by
      have h := (integral_indicator (μ := (volume : Measure ℝ))
        (s := Set.Ici a) (f := fun u => ‖F u‖))
      have h' := h measurableSet_Ici
      simpa using h'.symm
    have hind_int :
        Integrable (Set.indicator (Set.Ici a) (fun u => ‖F u‖)) :=
      hnorm.indicator measurableSet_Ici
    have hpoint :
        Set.indicator (Set.Ici a) (fun u => ‖F u‖)
            ≤ᵐ[volume] (fun u : ℝ => ‖F u‖) := by
      filter_upwards with u
      by_cases hu : u ∈ Set.Ici a
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    have hmono :=
        integral_mono_ae (μ := (volume : Measure ℝ))
          hind_int hnorm hpoint
    simpa [hEq] using hmono

  calc
    ‖A * (∫ u in Set.Ici a, F u)‖
        = ‖A‖ * ‖∫ u in Set.Ici a, F u‖ := hmul
    _   ≤ ‖A‖ * (∫ u in Set.Ici a, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hnormI (by simp)
    _   ≤ ‖A‖ * (∫ u : ℝ, ‖F u‖) :=
      mul_le_mul_of_nonneg_left hdom (by simp)

lemma fourier_decay_of_CS2
    (ψ : CS 2 ℂ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  let ψ' : W21 := (ψ : W21)
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u : ℝ, ‖𝓕 (ψ' : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
    simpa using (decay_bounds_cor (ψ := ψ'))
  refine ⟨C, ?_⟩
  intro u
  simpa [ψ'] using (hC u)

lemma integrable_norm_fourier_scaled_of_CS2
    (ψ : CS 2 ℂ) :
    Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
  obtain ⟨C, hdecay⟩ := fourier_decay_of_CS2 (ψ := ψ)
  have hC_nonneg : 0 ≤ C := by
    have h0 := hdecay 0
    have hnorm : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) 0‖ := norm_nonneg _
    have hC' : ‖𝓕 (ψ : ℝ → ℂ) 0‖ ≤ C := by simpa using h0
    exact hnorm.trans hC'
  have hmaj_int : Integrable (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    have hbase : Integrable (fun u : ℝ => (1 + u ^ 2)⁻¹) := integrable_inv_one_add_sq
    have hscale :
        Integrable (fun u : ℝ => (1 + (u / (2 * Real.pi)) ^ 2)⁻¹) :=
      hbase.comp_div (by nlinarith [Real.pi_pos])
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, pow_two] using
      hscale.const_mul C
  have hle :
      (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖)
        ≤ᵐ[volume]
      (fun u : ℝ => (C : ℝ) / (1 + (u / (2 * Real.pi))^2)) := by
    refine Filter.Eventually.of_forall ?_
    intro u
    simpa using (hdecay (u / (2 * Real.pi)))
  have hle_norm :
      (fun u : ℝ => ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖)
        ≤ᵐ[volume]
      (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) := by
    refine hle.mono ?_
    intro u hu
    have hden_pos : 0 < 1 + (u / (2 * Real.pi)) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (C : ℝ) / (1 + (u / (2 * Real.pi))^2) :=
      div_nonneg hC_nonneg hden_pos.le
    have hleft_nonneg : 0 ≤ ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖ := norm_nonneg _
    have hbound : ‖‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖‖ ≤
        (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg] using hu
    have hC_abs : |C| = C := abs_of_nonneg hC_nonneg
    have hden_abs : |1 + (u / (2 * Real.pi))^2| = 1 + (u / (2 * Real.pi))^2 := by
      have : 0 ≤ 1 + (u / (2 * Real.pi))^2 := by nlinarith
      simpa using abs_of_nonneg this
    have hnorm :
        ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
          (C : ℝ) / (1 + (u / (2 * Real.pi))^2) := by
      have hrec :
          ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖ =
            |C| / |1 + (u / (2 * Real.pi))^2| := by
        simp [Real.norm_eq_abs]
      simp [hC_abs, hden_abs, hrec]
    simpa [hnorm] using hbound
  have hmaj_int_norm :
      Integrable (fun u : ℝ => ‖(C : ℝ) / (1 + (u / (2 * Real.pi))^2)‖) :=
    hmaj_int.norm
  have hmeas :
      AEStronglyMeasurable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable.norm
  exact hmaj_int_norm.mono' hmeas hle_norm

lemma exists_bound_norm_G_on_tsupport
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (ψ : CS 2 ℂ) :
    ∃ K : ℝ, ∀ t : ℝ, t ∈ tsupport (ψ : ℝ → ℂ) →
      ‖G (1 + t * Complex.I)‖ ≤ K := by
  let s : Set ℝ := tsupport (ψ : ℝ → ℂ)
  have hscompact : IsCompact s := by
    simpa [s] using (ψ.h2.isCompact : IsCompact (tsupport (ψ : ℝ → ℂ)))
  have hphi_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by continuity
  have hphi_maps :
      Set.MapsTo (fun t : ℝ => (1 : ℂ) + t * Complex.I) s {z : ℂ | 1 ≤ z.re} := by
    intro t ht
    simp
  have hGcomp : ContinuousOn (fun t : ℝ => G ((1 : ℂ) + t * Complex.I)) s :=
    hG.comp hphi_cont.continuousOn hphi_maps
  have hnorm_contOn : ContinuousOn (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) s := hGcomp.norm
  have hbdd : BddAbove ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s) :=
    (hscompact.image_of_continuousOn hnorm_contOn).bddAbove
  refine ⟨sSup ((fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s), ?_⟩
  intro t ht
  have : ‖G ((1 : ℂ) + t * Complex.I)‖ ∈
      (fun t : ℝ => ‖G ((1 : ℂ) + t * Complex.I)‖) '' s := ⟨t, ht, rfl⟩
  exact le_csSup hbdd this

lemma norm_integrand_le_K_mul_norm_psi
    {x K : ℝ}
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
    ∀ t : ℝ,
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ ≤ K * ‖ψ t‖ := by
  intro t
  by_cases ht : t ∈ Function.support ψ
  · have hxnorm : ‖((x : ℂ) ^ (t * Complex.I))‖ = 1 := norm_x_cpow_it x t hx
    calc
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
          = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * ‖((x : ℂ) ^ (t * Complex.I))‖ := by
              simp [mul_left_comm, mul_comm]
      _   = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * 1 := by simp [hxnorm]
      _   ≤ K * ‖ψ t‖ := by
            have hGle : ‖G (1 + t * Complex.I)‖ ≤ K := hK t ht
            have : ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ ≤ K * ‖ψ t‖ :=
              mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have hψ0 : ψ t = 0 := by
      by_contra hψ0
      exact ht (by simpa [Function.support] using hψ0)
    simp [hψ0, mul_comm]

lemma norm_error_integral_le
    (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ)
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖) ) :
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
      ≤ K * (∫ t : ℝ, ‖ψ t‖) := by
  have h1 : ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := by
    simpa using (norm_integral_le_integral_norm
        (f := fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
  have hmeas_main : AEStronglyMeasurable
        (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) := by
    have hG' : AEMeasurable fun t : ℝ => G (1 + t * Complex.I) := hGline_meas.aemeasurable
    have hψ_meas' : AEMeasurable ψ := hψ_meas.aemeasurable
    have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            exact (continuous_ofReal.mul continuous_const).congr fun t => rfl
          simpa [mul_comm] using h)
      exact hcont.measurable.aemeasurable
    have hGψ_meas : AEMeasurable fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) := hG'.mul hψ_meas'
    have htotal : AEMeasurable (fun t : ℝ =>
            (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) :=
      hGψ_meas.mul hxpow_meas
    exact htotal.aestronglyMeasurable
  have hpt : (fun t : ℝ =>
          ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := by
    refine Eventually.of_forall ?_
    intro t
    exact norm_integrand_le_K_mul_norm_psi (hx := hx) (hK := hK) t
  have hR : Integrable (fun t : ℝ => K * ‖ψ t‖) := hψ.const_mul K
  have hL : Integrable (fun t : ℝ =>
        ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
      have hpt_norm :
          (fun t : ℝ => ‖‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖‖)
            ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := hpt.mono (by
          intro t ht
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using ht)
      exact hR.mono' hmeas_main.norm hpt_norm
  have h2 : (∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ ∫ t : ℝ, K * ‖ψ t‖ := integral_mono_ae (μ := (volume : Measure ℝ)) hL hR hpt
  have h3 : (∫ t : ℝ, K * ‖ψ t‖) = K * (∫ t : ℝ, ‖ψ t‖) := by
    simp [integral_const_mul]
  calc
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := h1
    _   ≤ ∫ t : ℝ, K * ‖ψ t‖ := h2
    _   = K * (∫ t : ℝ, ‖ψ t‖) := h3

lemma crude_upper_bound
    (hpos : 0 ≤ f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (ψ : CS 2 ℂ)
    (hψpos : ∀ y, 0 ≤ (𝓕 (ψ : ℝ → ℂ) y).re ∧ (𝓕 (ψ : ℝ → ℂ) y).im = 0) :
    ∃ B : ℝ, ∀ x : ℝ, 0 < x → ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤ B := by

  -- Integrability of ψ
  have hψ_int : MeasureTheory.Integrable (ψ : ℝ → ℂ) := by
    simpa using (ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2)
  have hψ_norm_int : MeasureTheory.Integrable (fun t : ℝ => ‖(ψ : ℝ → ℂ) t‖) :=
    hψ_int.norm
  have hψ_meas : MeasureTheory.AEStronglyMeasurable (ψ : ℝ → ℂ) :=
    hψ_int.aestronglyMeasurable

  -- Uniform bound K for ‖G(1+it)‖ on support ψ
  rcases exists_bound_norm_G_on_tsupport (G := G) hG ψ with ⟨K, hK_ts⟩
  have hK_support :
      ∀ t : ℝ, t ∈ Function.support (ψ : ℝ → ℂ) → ‖G (1 + t * Complex.I)‖ ≤ K := by
    have hbnG (hKts : ∀ t : ℝ, t ∈ tsupport ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
      ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K := by
      intro t ht
      exact hKts t ((subset_tsupport ψ) ht)
    exact hbnG hK_ts

  -- Measurability of the line restriction t ↦ G(1 + t I) from continuity-on
  have hGline_meas : Measurable (fun t : ℝ => G (1 + t * Complex.I)) := by
    have hline_cont : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by
      continuity
    have hmem : ∀ t : ℝ, ((1 : ℂ) + t * Complex.I) ∈ {s : ℂ | 1 ≤ s.re} := by
      intro t
      simp
    have hcont : Continuous (G ∘ fun t : ℝ => (1 : ℂ) + t * Complex.I) :=
      hG.comp_continuous hline_cont hmem
    simpa [Function.comp_def] using hcont.measurable

  -- L¹ bound for the scaled Fourier transform norm
  have hF_norm_int :
      MeasureTheory.Integrable (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
    integrable_norm_fourier_scaled_of_CS2 ψ
  have hF_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
    have hcont : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) u := by
      simpa using continuous_FourierIntegral (ψ : W21)
    have hcont_scaled : Continuous fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) :=
      hcont.comp (by continuity)
    exact hcont_scaled.aestronglyMeasurable
  have hF_int :
      MeasureTheory.Integrable (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) :=
    by
      have hfin_norm :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
        hF_norm_int.hasFiniteIntegral
      have hfin :
          MeasureTheory.HasFiniteIntegral
            (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))) := by
        simpa [MeasureTheory.hasFiniteIntegral_iff_norm] using hfin_norm
      exact ⟨hF_meas, hfin⟩
  refine ⟨K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
            + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖), ?_⟩
  intro x hx
  set I : ℂ := ∫ u in Set.Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)) with hI

  -- Lemma 12
  have hlim :=
    limiting_fourier_variant (f := f) (A := A) (G := G)
      hpos hG hG' hf ψ hψpos hx
  have hlim' :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
        - A * I
      = ∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I) := by
    simpa [hI] using hlim

  -- express the tsum as RHS + A*I
  have htsum :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
      = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    have h' :
        (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log (n / x)))
          = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I :=
      eq_add_of_sub_eq hlim'
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h'

  -- bound the RHS integral
  have hRHS_bound :
      ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖) :=
    norm_error_integral_le (G := G) (ψ := (ψ : ℝ → ℂ)) (x := x) (K := K)
      hGline_meas hψ_meas hx hK_support hψ_norm_int

  -- bound the A * I term
  have hA_bound :
      ‖A * I‖ ≤ ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hF_on : MeasureTheory.IntegrableOn
        (fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (Set.Ici (-Real.log x)) :=
      hF_int.integrableOn
    simpa [hI] using
      norm_mul_integral_Ici_le_integral_norm (A := A)
        (F := fun u : ℝ => 𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi)))
        (a := -Real.log x) hF_on hF_norm_int

  -- combine bounds
  have htsum_std :
      (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)))
        = (∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I := by
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htsum

  -- bound in the normalized form
  have hbound :
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
        ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) := by
    have hnorm :
        ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
            (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖ =
          ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ :=
      congrArg norm htsum_std
    calc
      ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ)
          (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x))‖
          = ‖(∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)) + A * I‖ := hnorm
      _ ≤ ‖∫ (t : ℝ), (G (1 + t * Complex.I)) * (ψ t) * x ^ (t * Complex.I)‖ + ‖A * I‖ :=
            norm_add_le _ _
      _ ≤ K * (∫ t : ℝ, ‖(ψ : ℝ → ℂ) t‖)
          + ‖A‖ * (∫ u : ℝ, ‖𝓕 (ψ : ℝ → ℂ) (u / (2 * Real.pi))‖) :=
            add_le_add hRHS_bound hA_bound
  exact hbound

set_option backward.isDefEq.respectTransparency false in
private lemma _root_.Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hf hg).bdd_mul
      (c := 1) ?_ ?_
    · exact (by continuity : Continuous _).aestronglyMeasurable
    · filter_upwards with p; simp
  calc ∫ v, 𝐞 (-(y * v)) • ∫ t, f t * g (v - t)
      = ∫ v, ∫ t, 𝐞 (-(y * v)) • (f t * g (v - t)) := by
        simp only [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ v, 𝐞 (-(y * v)) • (f t * g (v - t)) := integral_integral_swap h_int
    _ = ∫ t, f t • ∫ v, 𝐞 (-(y * v)) • g (v - t) := by
        simp only [Circle.smul_def, smul_eq_mul, mul_left_comm, integral_const_mul]
    _ = ∫ t, f t • ∫ u, 𝐞 (-(y * (u + t))) • g u := by
        congr 1; ext t
        rw [← integral_add_right_eq_self (fun v ↦ 𝐞 (-(y * v)) • g (v - t)) t]; simp
    _ = ∫ t, f t • ∫ u, (𝐞 (-(y * t)) * 𝐞 (-(y * u))) • g u := by
        congr 2 with t; congr 1
        simp only [mul_add, neg_add, mul_comm, Real.fourierChar.map_add_eq_mul]
    _ = ∫ t, 𝐞 (-(y * t)) • f t • ∫ u, 𝐞 (-(y * u)) • g u := by
        congr 1; ext t
        simp only [mul_smul, Circle.smul_def, smul_eq_mul, integral_const_mul]; ring
    _ = (∫ t, 𝐞 (-(y * t)) • f t) * ∫ u, 𝐞 (-(y * u)) • g u := by
        simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

private lemma _root_.Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
    𝓕 (fun x ↦ conj (f (-x))) y = conj (𝓕 f y) := by
  simp only [fourier_real_eq]
  have h_conj : ∀ x, 𝐞 (-(x * y)) • conj (f (-x)) = conj (𝐞 (x * y) • f (-x)) := fun x ↦ by
    simp only [Circle.smul_def, Real.fourierChar_apply, map_mul, smul_eq_mul, neg_mul,
      Complex.ofReal_neg, mul_neg]
    congr 1
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg]
  calc ∫ x, 𝐞 (-(x * y)) • conj (f (-x))
      = ∫ x, conj (𝐞 (x * y) • f (-x)) := by congr 1; ext x; exact h_conj x
    _ = conj (∫ x, 𝐞 (x * y) • f (-x)) := integral_conj
    _ = conj (∫ x, 𝐞 (-(x * y)) • f x) := by
        rw [← integral_neg_eq_self (fun x => 𝐞 (-(x * y)) • f x)]
        congr 2 with x; ring_nf

/-- Smooth compactly supported function with non-negative Fourier transform via self-convolution. -/
lemma auto_cheby_exists_smooth_nonneg_fourier_kernel :
    ∃ (ψ : ℝ → ℂ), ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) ∧ 0 < (𝓕 ψ 0).re := by
  obtain ⟨φ_real, hφSmooth, hφCompact, hφIcc, _, hφsupp⟩ :=
    smooth_urysohn_support_Ioo (a := 1/2) (b := 1) (c := 1) (d := 2) (by norm_num) (by norm_num)
  let φ : ℝ → ℂ := Complex.ofReal ∘ φ_real
  let φ_rev : ℝ → ℂ := fun x ↦ conj (φ (-x))
  let ψ_fun : ℝ → ℂ := convolution φ φ_rev (ContinuousLinearMap.mul ℝ ℂ) volume
  have hφSmooth' : ContDiff ℝ ∞ φ := contDiff_ofReal.comp hφSmooth
  have hφCompact' : HasCompactSupport φ := hφCompact.comp_left rfl
  have hφRevSmooth : ContDiff ℝ ∞ φ_rev := Complex.conjCLE.contDiff.comp (hφSmooth'.comp contDiff_neg)
  have hφRevCompact : HasCompactSupport φ_rev := (hφCompact'.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (by simp)
  have hφInt : Integrable φ := hφSmooth'.continuous.integrable_of_hasCompactSupport hφCompact'
  have hφRevInt : Integrable φ_rev := hφRevSmooth.continuous.integrable_of_hasCompactSupport hφRevCompact
  have hψSmooth : ContDiff ℝ ∞ ψ_fun := by
    convert hφRevCompact.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hφSmooth'.continuous.locallyIntegrable (μ := volume)) hφRevSmooth
  have hψCompact : HasCompactSupport ψ_fun :=
    HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℂ) hφCompact' hφRevCompact
  refine ⟨ψ_fun, hψSmooth, hψCompact, fun y ↦ ?_, ?_⟩
  · rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg y, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact ⟨Complex.normSq_nonneg _, rfl⟩
  · have hφ_nonneg : ∀ x, 0 ≤ φ_real x := fun x ↦ by
      have hx := hφIcc x; by_cases h : x ∈ Set.Icc (1:ℝ) 1
      · simp only [Set.indicator_of_mem h, Pi.one_apply] at hx; linarith
      · simp only [Set.indicator_of_notMem h] at hx; exact hx
    have hvol_supp : (1 : ENNReal) ≤ volume (Function.support φ_real) := by
      have hsub : Set.Ico (1:ℝ) 2 ⊆ Function.support φ_real := fun x hx ↦
        hφsupp.symm ▸ Set.mem_Ioo.mpr ⟨by linarith [hx.1], hx.2⟩
      calc _ = volume (Set.Ico (1:ℝ) 2) := by simp [Real.volume_Ico]; norm_num
           _ ≤ _ := volume.mono hsub
    have hφint_pos : 0 < ∫ x, φ_real x :=
      (integral_pos_iff_support_of_nonneg_ae (.of_forall hφ_nonneg)
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact)).2
        (lt_of_lt_of_le (by simp) hvol_supp)
    have hFφ0_re : 0 < (𝓕 φ 0).re := by
      simp only [φ, fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul,
        Function.comp_apply]
      have hint : Integrable (fun x => (φ_real x : ℂ)) :=
        (hφSmooth.continuous.integrable_of_hasCompactSupport hφCompact).ofReal
      calc (∫ x, (φ_real x : ℂ)).re = ∫ x, (φ_real x : ℂ).re := (integral_re hint).symm
        _ = ∫ x, φ_real x := by simp only [Complex.ofReal_re]
        _ > 0 := hφint_pos
    rw [Real.fourierIntegral_convolution hφInt hφRevInt, Pi.mul_apply,
      Real.fourierIntegral_conj_neg 0, mul_comm, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.normSq_pos.2 (fun h ↦ (ne_of_gt hFφ0_re) (by simp [h]))

/-- The series `∑ f(n)/n · 𝓕ψ(log(n/x)/(2π))` is summable for `x ≥ 1`. -/
lemma auto_cheby_fourier_summable (hpos : 0 ≤ f) (hf : ∀ σ', 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (x : ℝ) (hx : 1 ≤ x) :
    Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) := by
  let ψCS : CS 2 ℂ := ⟨ψ, hψSmooth.of_le (by norm_cast), hψCompact⟩
  let S : ℝ → ℂ := fun σ' ↦ ∑' n, term (f · : ℕ → ℂ) σ' n * 𝓕 ψCS.toFun (1 / (2 * π) * Real.log (n / x))
  let Pole : ℝ → ℂ := fun σ' ↦ (A : ℂ) * (x ^ (1 - σ') : ℝ) *
    ∫ u in Set.Ici (-Real.log x), (rexp (-u * (σ' - 1)) : ℂ) * 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))
  let RHS : ℝ → ℂ := fun σ' ↦ ∫ t : ℝ, G (σ' + t * I) * ψCS.toFun t * (x : ℂ) ^ (t * I)
  have l2 := limiting_fourier_lim2 (A := A) (x := x) ψCS hx
  have l3 := limiting_fourier_lim3 (G := G) hG ψCS hx
  have haux : (fun σ' ↦ S σ' - Pole σ') =ᶠ[𝓝[>] 1] RHS := eventually_nhdsWithin_of_forall fun σ' hσ' ↦ by
    simpa [S, Pole, RHS] using limiting_fourier_aux hG' hf ψCS hx σ' hσ'
  have hS_tendsto : Tendsto S (𝓝[>] 1) (𝓝 (RHS 1 + A * ∫ u in Set.Ici (-Real.log x),
      𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π)))) := by
    have hS_decomp :
        (fun σ' : ℝ => (S σ' - Pole σ') + Pole σ') =ᶠ[𝓝[>] 1] S := by
      exact Eventually.of_forall fun σ' => by simp
    simpa [Pole, RHS] using ((l3.congr' haux.symm).add l2).congr' hS_decomp
  have hbounded : BoundedAtFilter (𝓝[>] 1) (fun σ' ↦ ‖S σ'‖) := by
    simp only [BoundedAtFilter]
    let L := ‖RHS 1 + A * ∫ u in Set.Ici (-Real.log x), 𝓕 (W21.ofCS2 ψCS).toFun (u / (2 * π))‖
    have : ∀ᶠ σ' in 𝓝[>] 1, ‖S σ'‖ < L + 1 :=
      hS_tendsto.norm.eventually_lt tendsto_const_nhds (lt_add_one L)
    exact Asymptotics.IsBigO.of_bound (L + 1) (by filter_upwards [this] with σ h; simpa using h.le)
  let y : ℕ → ℝ := fun n ↦ (1 / (2 * π)) * Real.log (n / x)
  let w : ℕ → ℝ := fun n ↦ (𝓕 ψCS.toFun (y n)).re
  have hw : ∀ n, 0 ≤ w n := fun n ↦ (hψpos (y n)).1
  let rt : ℝ → ℕ → ℝ := fun σ n ↦ if n = 0 then 0 else f n / (n : ℝ) ^ σ * w n
  have rt_nn σ n : 0 ≤ rt σ n := by
    simp only [rt]; split_ifs with hn
    · rfl
    · exact mul_nonneg (div_nonneg (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero hn)) σ).le) (hw n)
  have hS_eq σ' (hσ' : 1 < σ') : S σ' = ↑(∑' n, rt σ' n) := by
    rw [Complex.ofReal_tsum]; apply tsum_congr; intro n
    simp only [rt, term, LSeries.term, y, w, one_div, mul_inv_rev]
    split_ifs with hn <;> simp only [hn, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul,
      Complex.ofReal_mul, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; congr 1
    exact Complex.ext rfl (hψpos _).2
  have hMono n : AntitoneOn (fun σ ↦ rt σ n) (Set.Ioi 1) := fun σ₁ _ σ₂ _ h ↦ by
    simp only [rt]; split_ifs with hn; · rfl
    apply mul_le_mul_of_nonneg_right _ (hw n)
    apply div_le_div_of_nonneg_left (hpos n) (Real.rpow_pos_of_pos (Nat.cast_pos.mpr
      (Nat.pos_of_ne_zero hn)) σ₁)
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)) h
  have hT_bdd : BoundedAtFilter (𝓝[>] 1) fun σ ↦ ∑' n, rt σ n := by
    rw [BoundedAtFilter, Asymptotics.isBigO_iff] at hbounded ⊢
    obtain ⟨C, hC⟩ := hbounded
    refine ⟨C, ?_⟩
    filter_upwards [hC, self_mem_nhdsWithin] with σ hnorm hσ
    rw [hS_eq σ hσ] at hnorm; simpa using hnorm
  have hSumm σ (hσ : 1 < σ) : Summable (rt σ ·) := by
    simpa [rt, w, y] using limiting_fourier_variant_lim1_aux ψCS hpos hf hψpos σ hσ
  have hSumm_1 : Summable (rt 1 ·) := by
    let σ_seq : ℕ → ℝ := fun k ↦ 1 + 1 / ((k : ℝ) + 1)
    have hσ_gt k : 1 < σ_seq k := by simp only [σ_seq, lt_add_iff_pos_right, one_div]; positivity
    have h_tendsto : Tendsto σ_seq atTop (𝓝[>] 1) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, by filter_upwards with k; exact hσ_gt k⟩
      have : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        simp only [one_div]; exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
      simpa [σ_seq] using tendsto_const_nhds.add this
    have h_ptwise n : Tendsto (fun k ↦ rt (σ_seq k) n) atTop (𝓝 (rt 1 n)) := by
      simp only [rt]; split_ifs with hn; · exact tendsto_const_nhds
      refine ((tendsto_const_nhds.rpow (tendsto_nhdsWithin_iff.mp h_tendsto).1 (Or.inl ?_)).inv₀
        (by simp [hn])).const_mul (f n) |>.mul_const (w n)
      exact (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hT_bdd.comp_tendsto h_tendsto)
    refine summable_of_sum_range_le (c := C) (rt_nn 1) fun m ↦ le_of_tendsto (tendsto_finsetSum _
        fun i _ ↦ h_ptwise i) ?_
    filter_upwards [h_tendsto.eventually self_mem_nhdsWithin, hC] with k hk hCk
    calc ∑ i ∈ Finset.range m, rt (σ_seq k) i
        ≤ ∑' n, rt (σ_seq k) n := (hSumm _ hk).sum_le_tsum _ fun n _ ↦ rt_nn _ n
      _ ≤ |∑' n, rt (σ_seq k) n| := le_abs_self _
      _ ≤ C := by simpa using hCk
  rw [show (fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))) =
      Complex.ofRealCLM ∘ (rt 1 ·) from ?_]
  · exact hSumm_1.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  ext n; simp only [rt, Real.rpow_one, one_div, w, y, Function.comp_apply]
  split_ifs with hn; · simp [hn]
  have him0 : (𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).im = 0 := (hψpos _).2
  have hre_eq : 𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x)) =
      Complex.ofReal ((𝓕 ψCS.toFun ((2 * π)⁻¹ * Real.log (n / x))).re) := by
    rw [← Complex.re_add_im (𝓕 ψCS.toFun _), him0]; simp
  conv_lhs => rw [show ψ = ψCS.toFun from rfl, hre_eq]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Short interval bound from global filtered bound: if `∑ f(n)/n · 𝓕ψ(log(n/x)) ≤ B`,
then `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for some `ε, C > 0`. -/
lemma auto_cheby_short_interval_bound (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (B : ℝ) (ψ : ℝ → ℂ) (hψSmooth : ContDiff ℝ ∞ ψ) (hψCompact : HasCompactSupport ψ)
    (hψpos : ∀ y, 0 ≤ (𝓕 ψ y).re ∧ (𝓕 ψ y).im = 0) (hψ0 : 0 < (𝓕 ψ 0).re)
    (hB_bound : ∀ x ≥ 1, ‖∑' n, f n / n * 𝓕 ψ (1 / (2 * Real.pi) * Real.log (n / x))‖ ≤ B) :
    ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x := by
  have hF : Continuous (𝓕 ψ) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by continuity) (hψSmooth.continuous.integrable_of_hasCompactSupport hψCompact)
  have hg : Continuous fun y ↦ (𝓕 ψ y).re := Complex.continuous_re.comp hF
  obtain ⟨δ, hδpos, hball⟩ := Metric.mem_nhds_iff.1 <|
    hg.continuousAt.preimage_mem_nhds (IsOpen.mem_nhds isOpen_Ioi (half_lt_self hψ0))
  let c := (𝓕 ψ 0).re / 2
  have hcpos : 0 < c := by dsimp only [c]; linarith
  have h_psi_ge_c : ∀ y, |y| < δ → c ≤ (𝓕 ψ y).re := fun y hy ↦ (hball (mem_ball_zero_iff.mpr hy)).le
  let ε := 1 - Real.exp (-2 * π * δ)
  have hε : 0 < ε ∧ ε < 1 := by
    have h1 : Real.exp (-2 * π * δ) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
    exact ⟨by simp only [ε]; linarith, by simp only [ε]; linarith [Real.exp_pos (-2 * π * δ)]⟩
  have hB_nonneg : 0 ≤ B := (norm_nonneg _).trans (hB_bound 1 le_rfl)
  refine ⟨ε, B / c + 1, hε.1, hε.2, by positivity, fun x hx ↦ ?_⟩
  have h_summable : Summable fun n ↦ (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x)) :=
    auto_cheby_fourier_summable hpos hf hG hG' ψ hψSmooth hψCompact hψpos x hx
  have hx_pos : 0 < x := by linarith
  have h_sum_lower : c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      ≤ ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ ?_
    · by_cases hn : (n : ℝ) ∈ Set.Ioc ((1 - ε) * x) x
      · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
        have hn_pos : 0 < (n : ℝ) := by nlinarith [hn.1, hε.2]
        let y := (1 / (2 * π)) * Real.log (n / x)
        have h_arg_small : |y| < δ := by
          have h2pi : 0 < 2 * π := by linarith [Real.pi_pos]
          simp only [y, abs_mul, abs_div, abs_one, abs_of_pos h2pi]
          field_simp [ne_of_gt h2pi]; rw [mul_comm, abs_lt]
          have h_log_lower : -2 * π * δ < Real.log (n / x) := by
            rw [← Real.log_exp (-2 * π * δ), Real.log_lt_log_iff (Real.exp_pos _) (by positivity)]
            have : Real.exp (-2 * π * δ) = 1 - ε := by simp only [ε]; ring
            rw [this]; field_simp; exact hn.1
          have h_log_upper : Real.log (n / x) ≤ 0 :=
            Real.log_nonpos (by positivity) (div_le_one_of_le₀ hn.2 hx_pos.le)
          constructor <;> nlinarith [Real.pi_pos]
        have h1 : x⁻¹ ≤ (n : ℝ)⁻¹ := by rw [inv_le_inv₀ hx_pos hn_pos]; exact hn.2
        have h2 : c ≤ (𝓕 ψ y).re := h_psi_ge_c y h_arg_small
        have hfn : 0 ≤ f n := hpos n
        have hre : 0 ≤ (𝓕 ψ y).re := (hψpos y).1
        have hn_inv : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn_pos.le
        calc c / x * f n = c * x⁻¹ * f n := by rw [div_eq_mul_inv]
          _ ≤ c * (n : ℝ)⁻¹ * f n := by gcongr
          _ ≤ (𝓕 ψ y).re * (n : ℝ)⁻¹ * f n := by gcongr
          _ = (n : ℝ)⁻¹ * (𝓕 ψ y).re * f n := by ring
          _ = f n / n * (𝓕 ψ y).re := by ring
      · rw [Set.indicator_of_notMem hn, mul_zero, mul_zero]
        exact mul_nonneg (div_nonneg (hpos n) (Nat.cast_nonneg n)) (hψpos _).1
    · refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun n hn ↦ ?_
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hn
      exact Nat.le_floor hn.2.2.1.2
    · rw [← Complex.summable_ofReal]; convert h_summable using 1; ext n
      rw [Complex.ofReal_mul, Complex.ofReal_div]
      norm_cast
      rw [Complex.ofReal_mul]
      congr 1
      apply Complex.ext
      · simp only [Complex.ofReal_re]
      · simp only [Complex.ofReal_im]; exact (hψpos _).2.symm
  have h_real_eq : ∑' n, f n / n * (𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re =
      (∑' n, (f n : ℂ) / n * 𝓕 ψ (1 / (2 * π) * Real.log (n / x))).re := by
    rw [Complex.re_tsum h_summable]; congr with n
    rw [Complex.mul_re]; norm_cast; simp only [zero_mul, sub_zero]
  calc ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)
      = x / c * (c / x * ∑' n, f n * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (n : ℝ)) := by
        field_simp [ne_of_gt hcpos, ne_of_gt hx_pos]
    _ ≤ x / c * B := by
        gcongr; rw [h_real_eq] at h_sum_lower
        exact h_sum_lower.trans ((Complex.re_le_norm _).trans (hB_bound x hx))
    _ = (B / c) * x := by field_simp [ne_of_gt hcpos]
    _ ≤ (B / c + 1) * x := by nlinarith

/-- Bootstraps short interval bounds to global Chebyshev bound via strong induction.
If `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for all `x ≥ 1`, then `∑_{n ≤ x} f(n) = O(x)`. -/
lemma auto_cheby_bootstrap_induction (hpos : 0 ≤ f)
    (h_short : ∃ (ε : ℝ) (C : ℝ), ε > 0 ∧ ε < 1 ∧ C > 0 ∧ ∀ x ≥ 1,
      ∑' n, (f n) * (Set.indicator (Set.Ioc ((1 - ε) * x) x) (fun _ ↦ 1) (n : ℝ)) ≤ C * x) :
    cheby f := by
  obtain ⟨ε, C₀, hε, hε1, hC₀, h_bound⟩ := h_short
  let C := C₀ / ε + f 0 + 1
  have hf0 : (0 : ℝ) ≤ f 0 := hpos 0
  have hdiv : 0 ≤ C₀ / ε := div_nonneg hC₀.le hε.le
  have hC : 0 ≤ C := by linarith
  refine ⟨C, fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n ih =>
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [cumsum]
    · simp only [cumsum, Finset.sum_range_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf0,
        Nat.cast_one, mul_one, C]
      linarith
  let x := (n : ℝ) - 1
  have hx : x ≥ 1 := by simp only [x, ge_iff_le, le_sub_iff_add_le]; norm_cast
  let m := ⌊(1 - ε) * x⌋₊ + 1
  have hm_lt : m < n := by
    simp only [m, x]
    have h1 : (1 - ε) * (n - 1 : ℝ) < (n - 1 : ℕ) := by
      calc (1 - ε) * (↑n - 1) < 1 * (↑n - 1) := by gcongr; linarith
        _ = ↑n - 1 := by ring
        _ = ↑(n - 1) := by simp [Nat.cast_sub (by omega : 1 ≤ n)]
    have h2 : ⌊(1 - ε) * (n - 1 : ℝ)⌋₊ < n - 1 :=
      (Nat.floor_lt (mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ n - 1))).mpr h1
    omega
  have hm_gt : (m : ℝ) > (1 - ε) * x := by
    simp only [m, Nat.cast_add, Nat.cast_one, gt_iff_lt]
    exact Nat.lt_floor_add_one ((1 - ε) * x)
  have h_decomp : cumsum (fun k ↦ ‖(f k : ℂ)‖) n = cumsum (fun k ↦ ‖(f k : ℂ)‖) m + ∑ k ∈ Finset.Ico m n, f k := by
    simp only [cumsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _),
      Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n)]
  have h_Ico : ∑ k ∈ Finset.Ico m n, f k ≤ C₀ * x := by
    calc ∑ k ∈ Finset.Ico m n, f k
        = ∑ k ∈ Finset.Ico m n, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          have ⟨hkm, hkn⟩ := Finset.mem_Ico.mp hk
          have hk_gt : (k : ℝ) > (1 - ε) * x := by linarith [hm_gt, (Nat.cast_le (α := ℝ)).mpr hkm]
          have hk_le : (k : ℝ) ≤ x := by
            have h1 : k ≤ n - 1 := Nat.le_pred_of_lt hkn
            have h2 : (k : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast h1
            simp only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, x] at h2 ⊢; exact h2
          simp only [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hk_gt, hk_le⟩), Pi.one_apply, mul_one]
      _ ≤ ∑' k, f k * Set.indicator (Set.Ioc ((1 - ε) * x) x) 1 (k : ℝ) := by
          refine Summable.sum_le_tsum _ (fun k _ ↦ mul_nonneg (hpos k) (Set.indicator_nonneg (by simp) _)) ?_
          refine summable_of_hasFiniteSupport <| (Set.finite_le_nat ⌊x⌋₊).subset fun k hk ↦ ?_
          simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Set.indicator_apply_ne_zero] at hk
          exact Nat.le_floor hk.2.1.2
      _ ≤ C₀ * x := h_bound x hx
  have hm_le : (m : ℝ) ≤ (1 - ε) * x + 1 := by
    have hpos' : 0 ≤ (1 - ε) * x := mul_nonneg (by linarith) (by linarith : (0 : ℝ) ≤ x)
    simp only [m, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hpos']
  have hnorm : ∀ k, ‖(f k : ℂ)‖ = f k := fun k ↦ by simp [abs_of_nonneg (hpos k)]
  simp only [hnorm] at h_decomp ih ⊢
  calc cumsum f n = cumsum f m + ∑ k ∈ Finset.Ico m n, f k := h_decomp
    _ ≤ C * m + C₀ * x := by linarith [ih m hm_lt, h_Ico]
    _ ≤ C * ((1 - ε) * x + 1) + C₀ * x := by nlinarith [hC]
    _ = (C * (1 - ε) + C₀) * x + C := by ring
    _ ≤ C * x + C := by
        have : C₀ ≤ C * ε := by
          calc C₀ = (C₀ / ε) * ε := by field_simp [ne_of_gt hε]
            _ ≤ (C₀ / ε + f 0 + 1) * ε := by gcongr; linarith [hpos 0]
            _ = C * ε := by simp only [C]
        nlinarith [hε, hε1, hx]
    _ ≤ C * n := by simp only [x]; ring_nf; linarith [hC]

lemma auto_cheby (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) : cheby f := by
  obtain ⟨ψ_fun, hψSmooth, hψCompact, hψpos, hψ0⟩ := auto_cheby_exists_smooth_nonneg_fourier_kernel
  obtain ⟨B, hB⟩ := crude_upper_bound hpos hG hG' hf ⟨ψ_fun, hψSmooth.of_le ENat.LEInfty.out, hψCompact⟩ hψpos
  exact auto_cheby_bootstrap_induction hpos <| auto_cheby_short_interval_bound hpos hf hG hG' B ψ_fun
    hψSmooth hψCompact hψpos hψ0 fun x hx ↦ hB x (by linarith)

end auto_cheby

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/PrimeNumberTheoremAnd/Consequences.lean` -/

section
set_option lang.lemmaCmd true

open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

lemma th43_b (x : ℝ) (hx : 2 ≤ x) :
    Nat.primeCounting ⌊x⌋₊ =
      θ x / log x + ∫ t in Set.Icc 2 x, θ t / (t * (Real.log t) ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

/-- If u ~ v and u-w = o(v) then w ~ v. -/
private theorem _root_.Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact Asymptotics.IsEquivalent.sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · change Tendsto (fun x : ℝ => (∑ n ∈ Icc 0 ⌊x⌋₊, Λ n) / (⌊x⌋₊ : ℝ))
          atTop (nhds 1)
        simpa [Function.comp_def, Finset.Iic_eq_Icc] using
          Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_ofPred_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2
      · rfl
      · rfl
      · rw [← sqrt_eq_rpow, div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · convert isLittleO_sqrt_mul_log.const_mul_left 2 using 1
    · rfl
    · rfl
    · ext x
      ring
    · ext x
      rfl

theorem chebyshev_asymptotic' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun t ↦ ε * t)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ (x : ℝ), θ x = x + f x := by
  have H := chebyshev_asymptotic
  rw [IsEquivalent, isLittleO_iff] at H
  let f := (fun x ↦ θ x - x)
  have integrable (x : ℝ) (hx : 2 ≤ x) : IntegrableOn f (Set.Icc 2 x) := by
    rw [IntegrableOn]
    refine Integrable.sub ?_ (ContinuousOn.integrableOn_Icc (continuousOn_id' _))
    refine Chebyshev.integrableOn_theta_div_id_mul_log_sq x |>.mul_continuousOn (g' := fun t => t * log t ^ 2)
      (ContinuousOn.mul (continuousOn_id' _) (ContinuousOn.pow (continuousOn_log |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) 2)) isCompact_Icc |>.congr_fun_ae ?_
    simp only [measurableSet_Icc, ae_restrict_eq, EventuallyEq, eventually_inf_principal]
    refine .of_forall fun t ⟨ht1, _⟩ => ?_
    rw [div_mul_cancel₀]
    simpa only [ne_eq, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
      log_eq_zero, _root_.or_self_left, not_or] using ⟨by linarith, by linarith, by linarith⟩
  refine ⟨f, fun ε hε ↦ ?_, integrable, ?_⟩
  · rw [isLittleO_iff]
    intro c hc
    specialize @H (c * ε) (mul_pos hc hε)
    simp only [Pi.sub_apply, norm_eq_abs, mul_assoc, eventually_atTop, norm_mul,
      abs_of_pos hε, f] at H ⊢
    exact H
  refine fun r => by simp [f]

theorem chebyshev_asymptotic'' :
    ∃ (f : ℝ → ℝ),
      (∀ ε > (0 : ℝ), (f =o[atTop] fun _ ↦ ε)) ∧
      (∀ (x : ℝ), 2 ≤ x → IntegrableOn f (Set.Icc 2 x)) ∧
      ∀ x > (0 : ℝ), θ x = x + x * (f x) := by
  obtain ⟨f, hf1, inte, hf2⟩ := chebyshev_asymptotic'
  refine ⟨fun t => f t / t, fun ε hε ↦ ?_, ?_, ?_⟩
  · simp only [isLittleO_iff, norm_eq_abs, norm_mul, eventually_atTop,
      norm_div] at hf1 ⊢
    intro r hr
    replace hf1 := hf1 ε hε
    obtain ⟨N, hN⟩ := hf1 hr
    use |N| + 1
    intro x hx
    have hx' : |N| + 1 ≤ |x| := by rwa [abs_of_nonneg (a := x) (le_trans (by positivity) hx)]
    rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hx'), mul_assoc]
    exact hN x (le_trans (le_trans (le_abs_self N) (by linarith)) hx)

  · intro x hx
    refine inte x hx |>.mul_continuousOn (g' := fun t : ℝ => t⁻¹)
      (continuousOn_inv₀ |>.mono <| by
        rintro t ⟨ht1, _⟩
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith) isCompact_Icc |>.congr_fun_ae <| .of_forall <| by simp [div_eq_mul_inv]
  intro x hx
  rw [hf2, mul_div_cancel₀]
  linarith

-- one could also consider adding a version with p < x instead of p \leq x

lemma continuousOn_log0 :
    ContinuousOn (fun x ↦ -1 / (x * log x ^ 2)) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma continuousOn_log1 : ContinuousOn (fun x ↦ (log x ^ 2)⁻¹ * x⁻¹) {0, 1, -1}ᶜ := by
  refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  fun_prop (disch := simp_all)

lemma integral_log_inv (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in a..b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in a..b, ((log t)^2)⁻¹ := by
  rw [le_iff_lt_or_eq] at hb
  rcases hb with hb | rfl; swap
  · simp only [intervalIntegral.integral_same, sub_self, add_zero]
  · have := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun x => (log x)⁻¹)
      (u' := fun x => -1 / (x * (log x)^2))
      (v := fun x => x)
      (v' := fun _ => 1) (a := a) (b := b)
      (fun x hx => by
        rw [Set.uIcc_eq_union, Set.Icc_eq_empty (lt_iff_not_ge |>.1 hb), Set.union_empty] at hx
        obtain ⟨hx1, _⟩ := hx
        rw [show (-1 / (x * log x ^ 2)) = (-1 / log x ^ 2) * (x⁻¹) by
          rw [mul_comm x]; field_simp]
        apply HasDerivAt.comp
          (h := fun t => log t) (h₂ := (fun t : ℝ => t)⁻¹) (x := x)
        · exact HasDerivAt.inv (c := fun t : ℝ => t) (c' := 1) (x := log x)
            (hasDerivAt_id' (log x))
            (by simp only [ne_eq, log_eq_zero, not_or]; refine ⟨?_, ?_, ?_⟩ <;> linarith)
        · apply hasDerivAt_log; linarith)
      (fun x _ => hasDerivAt_id' x)
      (by
        rw [intervalIntegrable_iff_integrableOn_Icc_of_le (le_of_lt hb)]
        apply ContinuousOn.integrableOn_Icc
        refine continuousOn_log0.mono fun x hx ↦ ?_
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] at hx ⊢
        refine ⟨?_, ?_, ?_⟩ <;> linarith)
      (by
        constructor <;>
        apply MeasureTheory.integrable_const)
    simp only [mul_one] at this
    rw [this]
    simp_rw [neg_div, neg_mul]
    rw [sub_eq_add_neg]
    congr 1
    rw [intervalIntegral.integral_of_le (le_of_lt hb),
      intervalIntegral.integral_of_le (le_of_lt hb),
      ← MeasureTheory.integral_neg]
    simp_rw [neg_neg]
    refine integral_congr_ae ?_
    · rw [ae_restrict_eq, eventuallyEq_inf_principal_iff]
      · refine .of_forall fun x hx => ?_
        simp only [Set.mem_Ioc, one_div, mul_inv_rev, mul_assoc] at hx ⊢
        rw [inv_mul_cancel₀, mul_one]
        linarith
      exact measurableSet_Ioc

lemma integral_log_inv' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) - ((log a)⁻¹ * a) +
      ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  have := integral_log_inv a b ha hb
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, if_pos hb, Set.uIoc_of_le hb,
    smul_eq_mul, one_mul] at this
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  rw [this]

lemma integral_log_inv'' (a b : ℝ) (ha : 2 ≤ a) (hb : a ≤ b) :
    (log a)⁻¹ * a + ∫ t in Set.Icc a b, (log t)⁻¹ =
    ((log b)⁻¹ * b) + ∫ t in Set.Icc a b, ((log t)^2)⁻¹ := by
  rw [integral_log_inv' a b ha hb]
  group

lemma integral_log_inv_pos (x : ℝ) (hx : 2 < x) :
    0 < ∫ t in Set.Icc 2 x, (log t)⁻¹ := by
  classical
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae]
  · simp only [Function.support_inv, measurableSet_Icc, Measure.restrict_apply']
    rw [show Function.support log ∩ Set.Icc 2 x = Set.Icc 2 x by
      rw [Set.inter_eq_right]
      intro t ht
      simp only [Set.mem_Icc, Function.mem_support, ne_eq, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩]
    simpa
  · simp only [measurableSet_Icc, ae_restrict_eq, EventuallyLE, eventually_inf_principal]
    refine .of_forall fun t (ht : _ ∧ _) => ?_
    simpa only [Pi.zero_apply, inv_nonneg] using log_nonneg (by linarith)
  · apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀
    · exact (continuousOn_log).mono <| by aesop

    · rintro t ⟨ht, -⟩
      simp only [ne_eq, log_eq_zero, not_or]
      exact ⟨by linarith, by linarith, by linarith⟩

lemma integral_log_inv_ne_zero (x : ℝ) (hx : 2 < x) :
    ∫ t in Set.Icc 2 x, (log t)⁻¹ ≠ 0 := by
  have := integral_log_inv_pos x hx
  linarith

lemma pi_asymp_aux (x : ℝ) (hx : 2 ≤ x) : Nat.primeCounting ⌊x⌋₊ =
    (log x)⁻¹ * θ x + ∫ t in Set.Icc 2 x, θ t * (t * log t ^ 2)⁻¹ := by
  rw [th43_b _ hx]
  simp_rw [div_eq_mul_inv, Chebyshev.theta_eq_sum_Icc]
  ring_nf!

theorem pi_asymp'' :
    (fun x => ((Nat.primeCounting ⌊x⌋₊ : ℝ) / ∫ t in Set.Icc 2 x, 1 / log t) - (1 : ℝ)) =o[atTop]
      fun _ => (1 : ℝ) := by
  obtain ⟨f, hf, f_int, hf'⟩ := chebyshev_asymptotic''
  have eq1 : ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      (∫ t in Set.Icc 2 x,
        (t + t * f t) * (t * log t ^ 2)⁻¹) := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [pi_asymp_aux x hx, hf' x (by linarith)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
    rw [hf' t (by grind)]

  replace eq1 :
    ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (log x)⁻¹ * (x + x * f x) +
      ((∫ t in Set.Icc 2 x, (log t ^ 2)⁻¹) +
        (∫ t in Set.Icc 2 x, (f t) * (log t ^ 2)⁻¹)) := by
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1]
    congr
    simp_rw [mul_inv_rev, add_mul]
    rw [MeasureTheory.integral_add]
    · congr 1
      all_goals
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        field [show t ≠ 0 by grind]
    · apply IntegrableOn.mul_continuousOn
        (hg := ContinuousOn.integrableOn_Icc <| continuousOn_id' _)
        (hK := isCompact_Icc)
      apply continuousOn_log1.mono ?_
      intro y h
      simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    · rw [show (fun t ↦ t * f t * ((log t ^ 2)⁻¹ * t⁻¹)) =
        fun t ↦ f t * (t * (log t ^ 2)⁻¹ * t⁻¹) by ext; ring]
      apply IntegrableOn.mul_continuousOn (hK := isCompact_Icc)
      · apply f_int x (by linarith)
      · simp_rw [mul_assoc]
        refine ContinuousOn.mul (continuousOn_id' (Set.Icc 2 x)) ?_
        apply continuousOn_log1.mono ?_
        intro y h
        simp only [Set.mem_Icc, Set.mem_compl_iff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at h ⊢
        exact ⟨by linarith, by linarith, by linarith⟩

  simp_rw [mul_add] at eq1
  simp_rw [show ∀ (x : ℝ),
    (log x)⁻¹ * x + (log x)⁻¹ * (x * f x) +
    ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) =
    ((log x)⁻¹ * x + (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
    ((log x)⁻¹ * (x * f x) +
      ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)
    by intros; ring] at eq1

  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      ⌊x⌋₊.primeCounting =
      (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
      ((log x)⁻¹ * (x * f x) +
        ∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) +
      C := by
    use ((log 2)⁻¹ * 2)
    filter_upwards [eq1, eventually_ge_atTop 2] with x eq1 hx
    rw [eq1, ← integral_log_inv'' _ _ (by rfl) hx]
    ring
  replace eq1 :
    ∃ (C : ℝ), ∀ᶠ (x : ℝ) in atTop,
      (⌊x⌋₊.primeCounting / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - 1 =
      ((log x)⁻¹ * (x * f x) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) +
      C / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
    obtain ⟨C, hC⟩ := eq1
    use C
    filter_upwards [hC, eventually_gt_atTop 2] with x hC hx
    rw [hC]
    field [integral_log_inv_ne_zero]
  simp_rw [isLittleO_iff] at hf
  choose C hC using eq1
  simp_rw [← one_div] at hC
  apply isLittleO_congr hC (by rfl) |>.mpr
  have ineq1 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c) : ∀ᶠ(x : ℝ) in atTop,
    (log x)⁻¹ * x * |f x| ≤ c * ε * ((log x)⁻¹ * x) := by
    filter_upwards [eventually_ge_atTop 2, hf ε hε hc] with x hx hM
    simp only [norm_eq_abs] at hM
    rw [abs_of_pos hε] at hM
    rw [mul_comm (c * ε)]
    gcongr
    bound
  have int_flog {a b : ℝ} (ha: 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ |f t| * (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    apply IntegrableOn.mul_continuousOn
    · apply Integrable.abs <| f_int b hb |>.mono (Set.Icc_subset_Icc_left ha) (by rfl)
    · refine ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
      · simp
        grind
      · intro t ht
        simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
    · exact isCompact_Icc
  have int_inv_log_sq {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      IntegrableOn (fun t ↦ (log t ^ 2)⁻¹) (Set.Icc a b) volume := by
    refine ContinuousOn.integrableOn_Icc <|
      ContinuousOn.inv₀ (ContinuousOn.pow (continuousOn_log |>.mono ?_) 2) ?_
    · grind
    · intro t ht
      simp only [Set.mem_Icc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, log_eq_zero, not_or] at ht ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
  simp_rw [eventually_atTop] at hf
  choose M hM using hf
  have ineq2 (ε : ℝ) (hε : 0 < ε) (c : ℝ) (hc : 0 < c)  :
    ∃ (D : ℝ),
      ∀ᶠ (x : ℝ) in atTop,
      |∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹| ≤
      c * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) + D := by
    use (((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), |f t| * (log t ^ 2)⁻¹) -
              c * ε * ∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹) +
            c * ε * ((log 2)⁻¹ * 2))
    filter_upwards [eventually_gt_atTop (max 2 (M ε hε hc))] with x hx
    calc _
      _ ≤ ∫ (t : ℝ) in Set.Icc 2 x, |f t * (log t ^ 2)⁻¹| :=
        norm_integral_le_integral_norm fun a ↦ f a * (log a ^ 2)⁻¹
      _ = ∫ (t : ℝ) in Set.Icc 2 x, |f t| * (log t ^ 2)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Icc fun t ht ↦ ?_
        rw [abs_mul, abs_of_nonneg (a := (log t ^ 2)⁻¹)]
        norm_num
        apply pow_nonneg
        exact log_nonneg <| by grind
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          |f t| * (log t ^ 2)⁻¹) := by
        rw [← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
        · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le, volume_singleton]
        · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
        · apply int_flog (by rfl) (le_max_left ..)
        · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ ≤ (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          (∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x,
          (c * ε) * (log t ^ 2)⁻¹) := by
          gcongr 1
          apply setIntegral_mono_on
          · apply int_flog (le_max_left ..) (le_trans (le_max_left ..) hx.le)
          · rw [IntegrableOn, integrable_const_mul_iff]
            · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
            · simp only [isUnit_iff_ne_zero, ne_eq, _root_.mul_eq_zero, not_or]
              exact ⟨by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ht
            simp only [Set.mem_Icc, sup_le_iff] at ht
            apply mul_le_mul_of_nonneg_right
            · refine hM ε hε hc t ht.1.2 |>.trans ?_
              simp only [norm_eq_abs, abs_of_pos hε, le_refl]
            · norm_num
              refine pow_nonneg (log_nonneg <| by linarith) 2
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) * ∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) := by
          congr 1
          exact integral_const_mul (c * ε) _
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc (max 2 (M ε hε hc)) x, (log t ^ 2)⁻¹) +
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) -
            ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
        ring
      _ = (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
          |f t| * (log t ^ 2)⁻¹) +
          ((c * ε) *
            ((∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹) -
              ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)))) := by
          congr 3
          rw [add_comm, ← setIntegral_union₀, Set.Icc_union_Icc_eq_Icc (le_max_left ..) hx.le]
          · rw [AEDisjoint, Set.Icc_inter_Icc_eq_singleton (le_max_left ..) hx.le,
              volume_singleton]
          · simp only [measurableSet_Icc, MeasurableSet.nullMeasurableSet]
          · apply int_inv_log_sq (by rfl) (le_max_left ..)
          · apply int_inv_log_sq (le_max_left ..) (le_trans (le_max_left ..) hx.le)
      _ = ((c * ε) * (∫ (t : ℝ) in Set.Icc 2 x, (log t ^ 2)⁻¹)) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        ring
      _ = ((c * ε) * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
            ((log 2)⁻¹ * 2) - ((log x)⁻¹ * x))) +
        ((∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)),
        |f t| * (log t ^ 2)⁻¹) -
        (c * ε) * (∫ (t : ℝ) in Set.Icc 2 (max 2 (M ε hε hc)), (log t ^ 2)⁻¹)) := by
        congr 2
        rw [integral_log_inv' _ _ (by rfl)]
        · ring
        · simp only [max_lt_iff] at hx
          linarith
      _ = _ := by ring
  choose D hD using ineq2

  have ineq4 (const : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x in atTop, |const / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| ≤ 1/2 * ε := by
    obtain rfl|hconst := eq_or_ne const 0
    · filter_upwards with x
      simp[hε.le]
    have ineq (x : ℝ) (hx : 2 < x) :=
      calc (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)
        _ ≥ (∫ (_ : ℝ) in Set.Icc 2 x, (log x)⁻¹) := by
          apply setIntegral_mono_on (integrable_const _)
          · refine ContinuousOn.integrableOn_Icc <|
              ContinuousOn.inv₀ (continuousOn_log |>.mono ?_) ?_
            · simp only [Set.subset_compl_singleton_iff, Set.mem_Icc, not_and, not_le,
              isEmpty_Prop, ofNat_pos, IsEmpty.forall_iff]
            · intro t ht
              simp only [Set.mem_Icc, ne_eq, log_eq_zero, not_or] at ht ⊢
              exact ⟨by linarith, by linarith, by linarith⟩
          · exact measurableSet_Icc
          · intro t ⟨ht1, ht2⟩
            gcongr
            bound
        _ = (x - 2) * (log x)⁻¹ := by
          rw [MeasureTheory.integral_const]
          simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, volume_Icc,
            smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff, sub_nonneg,
            inv_eq_zero, log_eq_zero, Measure.real]
          refine Or.inl (le_of_lt hx)

    simp_rw [abs_div]
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| / ((x - 2) * (log x)⁻¹) := by
      apply div_le_div₀ (abs_nonneg _) (by rfl)
      · apply mul_pos
        · linarith
        · norm_num
          rw [Real.log_pos_iff]
          · linarith
          · linarith
      · rw [abs_of_pos (integral_log_inv_pos _ hx)]
        exact ineq x hx
    have ineq (x : ℝ) (hx : 2 < x) :
        |const| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| ≤
        |const| * (log x / ((x - 2))) := by
      refine ineq x hx |>.trans <| le_of_eq ?_
      field_simp
    have lim := Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)
    simp only [pow_one, one_mul, ← sub_eq_add_neg] at lim
    rw [tendsto_atTop_nhds] at lim
    specialize lim (Metric.ball 0 ((1/2) * ε / |const| : ℝ)) (by
      simp only [Metric.mem_ball, _root_.dist_self]
      apply _root_.div_pos
      · linarith
      · simpa only [abs_pos, ne_eq]) Metric.isOpen_ball
    obtain ⟨M, hM⟩ := lim
    rw [eventually_atTop]
    refine ⟨max 3 M, ?_⟩
    intro x hx
    simp only [Metric.mem_ball, _root_.dist_zero_right, max_le_iff, norm_eq_abs] at hM hx
    refine ineq x (by linarith) |>.trans ?_
    specialize hM x hx.2
    rw [abs_of_nonneg (by
      apply div_nonneg
      · refine log_nonneg (by linarith)
      · linarith)] at hM
    have ineq' : |const| * (log x / (x - 2)) < |const| * ((1/2) * ε / |const|) := by
      rw [mul_lt_mul_iff_right₀]
      · exact hM
      · simpa only [abs_pos, ne_eq]
    rw [mul_div_cancel₀] at ineq'
    · refine le_of_lt ineq'
    · simpa only [ne_eq, abs_eq_zero]
  rw [isLittleO_iff]
  intro ε hε
  specialize ineq4 (|D ε hε (1/2) (by linarith)| + |C|) ε hε
  simp only [one_div, norm_eq_abs, norm_one, mul_one]
  filter_upwards [eventually_gt_atTop 2, ineq4, ineq1 ε hε (1 / 2) (by norm_num),
      hD ε hε (1 / 2) (by norm_num)] with x hx hB ineq1 hD
  have := integral_log_inv_pos x (by linarith) |>.le
  calc _
    _ ≤ |((log x)⁻¹ * (x * f x) / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹) /
          ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C / ∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      apply abs_add_three
    _ = |(log x)⁻¹ * (x * f x)| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| +
        |C| / |∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹| := by
      rw [abs_div, abs_div, abs_div]
    _ = |(log x)⁻¹ * (x * f x)| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        repeat rw [abs_of_pos <| integral_log_inv_pos _ (by linarith)]
    _ = ((log x)⁻¹ * x * |f x|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |(∫ (t : ℝ) in Set.Icc 2 x, f t * (log t ^ 2)⁻¹)| /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        congr
        rw [abs_mul, abs_mul, abs_of_nonneg (by bound), abs_of_nonneg (by linarith), mul_assoc]
    _ ≤ ((1/2) * ε * ((log x)⁻¹ * x)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        ((1/2) * ε * ((∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) - (log x)⁻¹ * x) +
          D ε hε (1/2) (by linarith)) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        |C| / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
        gcongr
    _ = ((1/2) * ε * (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹)) /
          (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) +
        (D ε hε (1/2) (by linarith) + |C|) / (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      ring
    _ = (1/2) * ε + (D ε hε (1/2) (by linarith) + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      congr 1
      rw [mul_div_assoc, div_self, mul_one]
      apply integral_log_inv_ne_zero
      linarith
    _ ≤ (1/2) * ε + (|D ε hε (1/2) (by linarith)| + |C|) /
        (∫ (t : ℝ) in Set.Icc 2 x, (log t)⁻¹) := by
      gcongr
      apply le_abs_self
    _ ≤ (1/2) * ε + (1/2) * ε := by
      rw [abs_div, abs_of_nonneg, abs_of_pos (a := ∫ _ in _, _)] at hB
      · gcongr
      · apply integral_log_inv_pos; linarith
      · positivity
    _ = ε := by
      field

theorem pi_asymp :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      ∀ᶠ (x : ℝ) in atTop,
        Nat.primeCounting ⌊x⌋₊ = (1 + c x) * ∫ t in (2 : ℝ)..x, 1 / (log t) := by
  refine ⟨_, pi_asymp'', ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  rw [intervalIntegral.integral_of_le (by linarith),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  field [(integral_log_inv_pos x (by linarith)).ne']

lemma inv_div_log_asy : ∃ c, ∀ᶠ (x : ℝ) in atTop,
    ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2 ≤ c * (x / log x ^ 2) := by
  have := Chebyshev.integral_one_div_log_sq_isBigO
  rw [isBigO_iff] at this
  obtain ⟨c, hc⟩ := this
  use c
  filter_upwards [hc, eventually_ge_atTop 2] with x hc hx
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx]
  apply le_trans (by apply le_norm_self)
  nth_rewrite 2 [norm_of_nonneg (by positivity)] at hc
  exact hc

lemma integral_log_inv_pialt (x : ℝ) (hx : 4 ≤ x) : ∫ (t : ℝ) in Set.Icc 2 x, 1 / log t =
    x / log x - 2 / log 2 + ∫ (t : ℝ) in Set.Icc 2 x, 1 / (log t) ^ 2 := by
  have := integral_log_inv 2 x (by norm_num) (by linarith)
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hx]),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx]),
    ← mul_one_div, one_div, ← mul_one_div, one_div]
  simp only [one_div, this, mul_comm]

lemma integral_div_log_asymptotic : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1:ℝ)) ∧
    ∀ᶠ (x : ℝ) in atTop, ∫ t in Set.Icc 2 x, 1 / (log t) = (1 + c x) * x / (log x) := by
  obtain ⟨c, hc⟩ := inv_div_log_asy
  use fun x => ((∫ (t : ℝ) in Set.Icc 2 x, 1 / log t ^ 2) - 2 / log 2) * log x / x
  constructor
  · simp_rw [mul_div_assoc, mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _|>.mpr
    · simp_rw [one_div_div]
      apply IsLittleO.sub
      · apply IsBigO.trans_isLittleO (g := (fun x ↦ x / log x ^ 2))
        · rw [isBigO_iff]
          use c
          filter_upwards [eventually_ge_atTop 2, hc] with x hx hc
          simp only [norm_eq_abs]
          rwa [abs_of_nonneg, abs_of_nonneg]
          · bound
          · apply setIntegral_nonneg measurableSet_Icc fun t ht ↦ (by bound)
        apply isLittleO_of_tendsto
        · simp
        apply tendsto_log_atTop.inv_tendsto_atTop.congr'
        filter_upwards [eventually_ne_atTop 0] with x hx
        simp only [Pi.inv_apply]
        field
      apply isLittleO_mul_iff_isLittleO_div _|>.mp
      · conv => arg 2; ext; rw [mul_comm]
        apply IsLittleO.const_mul_left isLittleO_log_id_atTop
      · filter_upwards [eventually_ge_atTop 2] with x hx
        simp; grind
    filter_upwards [eventually_ge_atTop 2] with x hx
    simp
    grind
  · filter_upwards [eventually_ge_atTop 4] with x hx
    rw [integral_log_inv_pialt x hx]
    field [show log x ≠ 0 by simp; grind]

theorem pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
  obtain ⟨f, hf, h⟩ := pi_asymp
  obtain ⟨f', hf', h'⟩ := integral_div_log_asymptotic
  use (fun x => (log x / x) * ⌊x⌋₊.primeCounting - 1)
  constructor
  · apply IsLittleO.congr' (f₁ := (fun x ↦ f x + f x * f' x + f' x)) _ _ (by rfl)
    · apply IsLittleO.add _ hf'
      apply IsLittleO.add hf
      simpa [Pi.mul_apply, one_mul] using hf.mul hf'
    · filter_upwards [eventually_ge_atTop 2, h, h'] with x hx h h'
      rw [h, intervalIntegral.integral_of_le hx, ← integral_Icc_eq_integral_Ioc, h']
      have : log x ≠ 0 := by simp; grind
      field
  · intro x
    obtain rfl|hx := eq_or_ne x 0
    · simp
    obtain rfl|hx := eq_or_ne x 1
    · simp
    obtain rfl|hx := eq_or_ne x (-1 : ℝ)
    · simp
      norm_num
    have : log x ≠ 0 := by simp_all
    field

lemma prime_in_gap' (a b : ℕ) (h : a.primeCounting < b.primeCounting)
    : ∃ (p : ℕ), p.Prime ∧ (a + 1) ≤ p ∧ p < (b + 1) := by
  obtain ⟨p, hp, pp⟩ := exists_of_count_lt_count h
  exact ⟨p, pp, hp.left, hp.right⟩

lemma prime_in_gap (a b : ℝ) (ha : 0 < a)
    (h : ⌊a⌋₊.primeCounting < ⌊b⌋₊.primeCounting)
    : ∃(p : ℕ), p.Prime ∧ a < p ∧ p ≤ b := by

  have hab : ⌊a⌋₊ < ⌊b⌋₊ := Monotone.reflect_lt Nat.monotone_primeCounting h
  obtain ⟨w, h, ha, hb⟩ := prime_in_gap' ⌊a⌋₊ ⌊b⌋₊ h
  refine ⟨w, h, lt_of_floor_lt ha, ?_⟩
  have : a < b := by
    by_contra h
    cases lt_or_eq_of_le <| le_of_not_gt h with
    | inl hh => linarith [floor_le_floor <| le_of_lt hh]
    | inr hh =>
      rw [hh] at hab
      rwa [←lt_self_iff_false ⌊a⌋₊]
  by_contra h
  have : ⌊b⌋₊ < w := floor_lt (by linarith) |>.mpr (lt_of_not_ge h)
  have : ⌊b⌋₊ + 1 ≤ w := by linarith
  linarith

lemma bound_f_second_term (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 + f x) < (1 + δ) := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) < 1 + z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p

  rw [Filter.eventually_atTop]

  use a
  intro b hb
  exact bound_one_plus_f b δ (ha b (by linarith))

lemma bound_f_first_term {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x: ℝ in atTop, (1 + f ((1 + ε) * x)) > (1 - δ)  := by
  have bound_one_plus_f: ∀ y: ℝ, ∀ z: ℝ, |f y| < z → 1 + (f y) > 1 - z := by
    intro y z hf
    by_cases f_pos: 0 < f y
    · rw [abs_of_pos f_pos] at hf
      linarith
    · rw [not_lt] at f_pos
      rw [abs_of_nonpos f_pos] at hf
      linarith

  have f_small := NormedAddGroup.tendsto_nhds_zero.mp hf δ hδ
  simp only [norm_eq_abs, eventually_atTop] at f_small
  obtain ⟨p, hp⟩ := f_small

  let a := ((max 1 p) : ℝ)
  have ha: ∀ b: ℝ, a ≤ b → |f b| < δ := by
    intro b hb
    have b_ge_p: p ≤ b := by
      have a_ge_p: p ≤ a := by simp [a]
      linarith
    exact hp b b_ge_p

  rw [Filter.eventually_atTop]

  use a
  intro b hb

  have a_pos: 0 < a := by
    simp [a]

  have pos_mul: ∀ x y z : ℝ, 0 < x → 0 < y → 1 < z → x ≤ y → x < y * z := by
    intro x y z _ hy hz hlt
    have y_lt: y < y * z := by
      exact (lt_mul_iff_one_lt_right hy).mpr hz
    linarith

  have mul_increase: a ≤ (1 + ε) * b := by
    simp only [a] at hb
    have a_le := pos_mul a b (1 + ε) a_pos (by linarith) (by linarith) (by linarith)
    linarith

  exact bound_one_plus_f ((1 + ε) * b) δ (ha ((1 + ε) * b) mul_increase)

lemma smaller_terms {ε : ℝ} (hε : 0 < ε) (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ)
    (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop, (1 - δ) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) <
      (1 + f ((1 + ε) * x)) * ((1 + ε) * x / (Real.log ((1 + ε) * x))) := by
  have first_term := bound_f_first_term hε f hf δ hδ
  simp only [gt_iff_lt, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [eventually_atTop]
  let a := max p 1
  have ha: ∀ (b : ℝ), a ≤ b → 1 - δ < 1 + f ((1 + ε) * b) := by
    intro b hb
    have a_ge_p: p ≤ a := by
      simp [a]
    specialize hp b (by linarith)
    exact hp
  use a
  intro b hb
  rw [mul_lt_mul_iff_left₀]
  · exact ha b hb
  · simp only [sup_le_iff, a] at hb
    have b_ge_one: 1 ≤ b := hb.2
    have log_pos: Real.log ((1 + ε) *b) > 0 := by
      have one_pplus_pos: 1 < (1 + ε) := by linarith
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · exact one_lt_mul_of_lt_of_le one_pplus_pos b_ge_one

    positivity

lemma second_smaller_terms (f : ℝ → ℝ) (hf : Tendsto f atTop (nhds 0)) (δ : ℝ) (hδ : δ > 0) :
    ∀ᶠ x : ℝ in atTop,
      (1 + δ) * (x / Real.log x) > (1 + f x) * (x / Real.log x) := by
  have first_term := bound_f_second_term f hf δ hδ

  simp only [_root_.add_lt_add_iff_left, eventually_atTop] at first_term
  obtain ⟨p, hp⟩ := first_term
  simp only [gt_iff_lt, eventually_atTop]
  let a := max p 2
  have ha: ∀ (b : ℝ), a ≤ b → 1 + δ > 1 + f ( b) := by
    intro b hb
    have a_ge_p: p <= a := by simp [a]
    specialize hp b (by linarith)
    linarith
  use a
  intro b hb
  specialize ha b hb
  have rhs_nonzero:  b / log ( b) > 0 := by
    simp only [sup_le_iff, a] at hb
    obtain ⟨_, hb2⟩ := hb
    have log_pos: Real.log (b) > 0 := by
      refine (Real.log_pos_iff ?_).mpr ?_
      · positivity
      · linarith
    positivity
  rw [mul_lt_mul_iff_left₀]
  · exact ha
  · linarith

lemma x_log_x_atTop : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
  have inv_log_x_div := Filter.Tendsto.comp (f := fun x => Real.log x / x) (g := fun x => x⁻¹)
    (x := Filter.atTop) (y := (nhdsWithin 0 (Set.Ioi 0))) (z := Filter.atTop) ?_ ?_
  · simp_rw [Function.comp_def, inv_div] at inv_log_x_div
    exact inv_log_x_div
  · exact tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have log_div_x := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by simp)
      simp only [pow_one, one_mul, add_zero] at log_div_x
      exact log_div_x
    · simp only [Set.mem_Ioi, eventually_atTop]
      use 2
      intro x hx
      have log_pos: 0 < Real.log x := by
        refine (Real.log_pos_iff ?_).mpr ?_ <;> linarith
      positivity

lemma tendsto_by_squeeze (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun (x : ℝ) => (Nat.primeCounting ⌊(1 + ε) * x⌋₊ : ℝ) -
      (Nat.primeCounting ⌊x⌋₊ : ℝ)) atTop atTop := by
  obtain ⟨c, hc, pi_x_eq⟩ := pi_alt
  rw [Asymptotics.isLittleO_iff_tendsto (by simp)] at hc
  conv =>
    arg 1
    intro x
    rw [pi_x_eq]
    rw [pi_x_eq]
  simp only [div_one] at hc

  -- (1 + δ) * (( x / (Real.log (x)))) > (1 + f ( x)) * ( x / (Real.log (x)))

  let d: ℝ := ε/(2*(2 + ε))
  have hd: 0 < d := by positivity
  have first_helper := smaller_terms hε c hc (d) hd
  have second_helper := second_smaller_terms c hc d hd

  apply Filter.tendsto_atTop_mono' (f₁ := fun x => (
      ((1 - d) * ((1 + ε) * x / log ((1 + ε) * x)))
      -
      ((1 + d) * (x / log x)))
    )
  · rw [Filter.EventuallyLE]

    simp only [eventually_atTop] at first_helper
    simp only [gt_iff_lt, eventually_atTop] at second_helper

    obtain ⟨a1, ha1⟩ := first_helper
    obtain ⟨a2, ha2⟩ := second_helper

    simp only [eventually_atTop]

    use (max a1 a2)
    intro b hb

    have lt_compare: ∀ a b c d : ℝ, a < c ∧ b > d → a - b ≤ c - d := by
      intro a b c d h_lt
      obtain ⟨a_lt, b_gt⟩ := h_lt
      linarith

    apply lt_compare
    simp only [sup_le_iff] at hb
    specialize ha1 b hb.1
    specialize ha2 b hb.2
    field_simp
    field_simp at ha1 ha2
    exact ⟨ha1, ha2⟩
  · rw [← Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
    have log_split: ∀ x: Set.Ioi 1, x.val / log ((1 + ε) * x.val) =
      x.val / (log (1 + ε) + log (x.val)) := by
      intro x
      have x_ge_one: 1 < x.val := Set.mem_Ioi.mp x.property
      rw [Real.log_mul (by linarith) (by linarith)]

    have log_factor: ∀ x: Set.Ioi 1, x.val / (log (1 + ε) + log (x.val)) =
      x.val / ((1 + (log (1 + ε)/(log x.val))) * (log x.val)) := by
      intro x
      have : log (x.val) ≠ 0 := by
        have pos := Real.log_pos x.property
        linarith
      field_simp
      rw [add_comm]

    conv at log_factor =>
      intro x
      rhs
      rw [div_mul_eq_div_mul_one_div]

    conv =>
      arg 1
      intro x
      lhs
      rw [mul_div_assoc]
      rw [log_split x]

    conv =>
      arg 1
      intro x
      lhs
      rw [log_factor]

    suffices Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ (1 - d) * ((1 + ε) * x) /
      ((1 + log (1 + ε) / log x) * log x) - (1 + d) * x / log x) atTop atTop by
      field_simp at this ⊢
      exact this
    conv =>
      arg 1
      intro x
      rw [sub_eq_add_neg]
      rw [← neg_div]
      rw [div_add_div]
      · skip
      tactic =>
        simp only [ne_eq, _root_.mul_eq_zero, log_eq_zero, not_or]
        have x_pos := x.property
        simp_rw [Set.Ioi, Set.mem_ofPred_eq] at x_pos
        refine ⟨?_, by linarith, by linarith, by linarith⟩
        have log_num_pos: 0 < log (1 + ε) := by
          exact Real.log_pos (by linarith)
        have log_denom_pos: 0 < log x := by
          exact Real.log_pos x.property
        positivity
      tactic =>
        have pos := Real.log_pos (x.property)
        linarith

    conv =>
      arg 1
      intro x
      equals ↑x * (log ↑x * ((1 + ε) * (1 - d)) -
          (1 + log (1 + ε) / log ↑x) * ((1 + d) * log ↑x)) /
        (log ↑x * ((1 + log (1 + ε) / log ↑x) * log ↑x)) =>
        ring

    simp only [mul_div_mul_comm]
    conv =>
      arg 1
      intro x
      rw [mul_comm]

    apply Filter.Tendsto.pos_mul_atTop (C := (1 + ε) * (1 - d) - (1 + d))
    · simp only [d, sub_pos]
      field_simp
      ring_nf
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      apply lt_of_sub_pos
      ring_nf
      positivity
    · conv =>
        arg 1
        intro x
        lhs
        rhs
        equals (log x.val) * ((1 + log (1 + ε) / log ↑x) * ((1 + d))) =>
          ring

      simp_rw [← mul_sub]
      conv =>
        arg 1
        intro x
        rhs
        rw [mul_comm]

      simp only [mul_div_mul_comm]
      conv =>
        arg 1
        intro x
        lhs
        equals 1 =>
          have log_pos := Real.log_pos x.property
          field_simp

      simp only [one_mul]
      conv =>
        arg 3
        equals nhds (((1 + ε) * (1 - d) - (1 + d)) / 1) => simp

      apply Filter.Tendsto.div
      · apply Filter.Tendsto.sub
        · simp
        · conv =>
            arg 3
            equals nhds (1 * (1 + d)) => simp
          apply Filter.Tendsto.mul
          · conv =>
              arg 3
              equals nhds (1 + 0) => simp
            apply Filter.Tendsto.add
            · simp
            · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
              · simp
              · simp only [tendsto_comp_val_Ioi_atTop]
                exact tendsto_log_atTop
          · simp
      · conv =>
          arg 3
          equals nhds (1 + 0) => simp
        apply Filter.Tendsto.add
        · simp
        · apply Filter.Tendsto.div_atTop (a := log (1 + ε))
          · simp
          · simp only [tendsto_comp_val_Ioi_atTop]
            exact tendsto_log_atTop
      · simp
    · let x_div_log (x: ℝ) := x / Real.log x
      conv =>
        arg 1
        equals (fun (x : Set.Ioi 1) => x_div_log x.val) => rfl

      rw [Filter.tendsto_comp_val_Ioi_atTop (a := 1)]
      exact x_log_x_atTop

theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  have squeeze := tendsto_by_squeeze (ε/2) (by linarith)
  rw [Filter.tendsto_iff_forall_eventually_mem] at squeeze
  specialize squeeze (Set.Ici 1) (by exact Ici_mem_atTop 1)
  simp only [Set.mem_Ici, eventually_atTop] at squeeze
  obtain ⟨a, ha⟩ := squeeze
  rw [eventually_atTop]
  use (max a 1)
  intro b hb
  have hb' : a ≤ b ∧ 1 ≤ b := max_le_iff.mp hb
  specialize ha b hb'.1

  have val_lt : (⌊b⌋₊.primeCounting : ℝ) < ⌊(1 + ε/2) * b⌋₊.primeCounting := by linarith
  norm_cast at val_lt

  have jump := prime_in_gap b ((1 + ε/2) * b) (by linarith) val_lt
  obtain ⟨p, hp, b_lt_p, p_le⟩ := jump
  have p_lt: p < (1 + ε) * b := by
    linarith
  use p

noncomputable def R (x : ℝ) : ℝ := Psi x - x

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos862.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 862.
https://www.erdosproblems.com/forum/thread/862

Informal authors:
- David Saxton
- Andrew Thomason
- ChatGPT

Statement authors:
- Aristotle

Formal authors:
- Aristotle
- Boris Alexeev
- Kevin Barreto

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos862.md
-/
/-
We formalized the proof that there are many maximal Sidon subsets of an interval.
Key results include:
- `lem_extend`: Every Sidon set is contained in a maximal Sidon set.
- `lem_cover`: A bound relating A(N), A_1(N), and f(N).
- `lem_ruzsa_group` and `lem_modular`: Construction of modular Sidon sets.
- `lem_four_block`: A construction lifting modular Sidon sets to integers.
- `prop_lower_special_ineq`: Lower bound for A(N) at special N.
- `eventually_lower_bound`: Lower bound for A(N) for all large N.
- `thm_main`: The main lower bound for A_1(N).
- `cor_answers_1` and `cor_answers_2`: Corollaries regarding the growth of A_1(N).

In `eventually_lower_bound`, we avoid issues with `liminf` in `Real` for
potentially unbounded sequences. The main theorem and corollaries follow from
this bound.
-/

namespace Erdos862

set_option maxHeartbeats 1000000
-- Several Sidon counting and covering proofs time out at the default heartbeat limit.

open scoped BigOperators

noncomputable section

open Real Filter Asymptotics

theorem prime_between {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
  exact _root_.Erdos43.prime_between hε

/-- A Sidon set: any equation a+b=c+d with all terms in S forces {a,b}={c,d}. -/
def Sidon {α : Type} [AddCommMonoid α] (S : Set α) : Prop :=
  ∀ a b c d, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a + b = c + d → ({a, b} : Set α) = {c, d}

/-- Sidon modulo M: the image of S in ZMod M is Sidon. -/
def SidonMod (M : ℕ) (S : Set ℕ) : Prop :=
  Sidon ((fun x : ℕ => (x : ZMod M)) '' S)

/-- f(N): maximum size of a Sidon subset of [1..N]. -/
noncomputable def f (N : ℕ) : ℕ :=
  let rangeN : Finset ℕ := Finset.Icc 1 N
  letI : DecidablePred (fun A => Sidon (A : Set ℕ)) := Classical.decPred _
  let sidonSets : Finset (Finset ℕ) :=
    rangeN.powerset.filter (fun A => Sidon (A : Set ℕ))
  sidonSets.sup Finset.card

/-- Sidon of order h: sums of h elements determine multisets. -/
def SidonOfOrder {α : Type*} [AddCommMonoid α] (h : ℕ) (S : Set α) : Prop :=
  ∀ u v : Fin h → α, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) →
    (∑ i, u i) = (∑ i, v i) → List.Perm (List.ofFn u) (List.ofFn v)

/-- Sidon of order h modulo M. -/
def SidonModOfOrder (h M : ℕ) (S : Set ℕ) : Prop :=
  SidonOfOrder h ((fun n : ℕ => (n : ZMod M)) '' S)

section ErdosTuran

/-- Inequality for Sidon sets derived from the difference set argument. -/
lemma erdos_turan_inequality {N m : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hSidon : Sidon (A : Set ℕ)) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card ^ 2 : ℝ) ≤ (N + m : ℝ) * (A.card / m + 1) := by
  have h_cauchy_schwarz :
      ((Finset.card A * m : ℝ)) ^ 2 ≤
      ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
      ((Finset.card A * m : ℝ) + (m * (m - 1))) := by
    have h_cs_inner :
        ((Finset.card A * m : ℝ)) ^ 2 ≤
        ((Finset.card (Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A))) : ℝ) *
        ((∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2)) := by
      have h_cs : ∀ (S : Finset ℕ) (g : ℕ → ℝ),
          (∑ x ∈ S, g x) ^ 2 ≤ (Finset.card S : ℝ) * ∑ x ∈ S, g x ^ 2 := by
        intro S g
        have := Finset.sum_le_sum fun x (_ : x ∈ S) =>
          mul_self_nonneg (g x - (∑ y ∈ S, g y) / S.card)
        by_cases hS : S = ∅
        · simp_all
        · have hne : (S.card : ℝ) ≠ 0 := by
            exact Nat.cast_ne_zero.mpr <| Finset.card_ne_zero_of_mem <|
              Classical.choose_spec <| Finset.nonempty_of_ne_empty hS
          have h2 : (∑ y ∈ S, g y) / ↑S.card * ↑S.card = ∑ y ∈ S, g y := by
            rw [mul_comm]; exact mul_div_cancel₀ (∑ y ∈ S, g y) hne
          have h_exp : ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2 =
              ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card := by
            calc ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2
                = ∑ x ∈ S, (g x ^ 2 - 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) +
                    ((∑ y ∈ S, g y) / ↑S.card) ^ 2) := by congr 1 with x; rw [sub_sq]
              _ = ∑ x ∈ S, g x ^ 2 - ∑ x ∈ S, 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) +
                    ∑ x ∈ S, ((∑ y ∈ S, g y) / ↑S.card) ^ 2 := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = ∑ x ∈ S, g x ^ 2 - 2 * ((∑ y ∈ S, g y) / ↑S.card) * (∑ x ∈ S, g x) +
                    ↑S.card * ((∑ y ∈ S, g y) / ↑S.card) ^ 2 := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  have : ∑ x ∈ S, 2 * g x * ((∑ y ∈ S, g y) / ↑S.card) =
                      2 * ((∑ y ∈ S, g y) / ↑S.card) * (∑ x ∈ S, g x) := by
                    rw [Finset.mul_sum]; congr 1 with x; ring
                  rw [this]
              _ = ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card := by
                  rw [sq]; field_simp [hne]; ring
          have h_ge : ∑ x ∈ S, (g x - (∑ y ∈ S, g y) / ↑S.card) ^ 2 ≥ 0 := by
            refine Finset.sum_nonneg fun x _ => sq_nonneg _
          rw [h_exp] at h_ge
          have hScard : (S.card : ℝ) > 0 := Nat.cast_pos.mpr (Finset.card_pos.mpr
            (Finset.nonempty_of_ne_empty hS))
          have h_expand : ↑S.card * (∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 / ↑S.card) =
              ↑S.card * ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 := by field_simp [hne]
          have h_prod : ↑S.card * ∑ x ∈ S, g x ^ 2 - (∑ y ∈ S, g y) ^ 2 ≥ 0 := by
            rw [← h_expand]; exact mul_nonneg (le_of_lt hScard) h_ge
          nlinarith [sq_nonneg (∑ y ∈ S, g y)]
      convert h_cs _ _ using 2
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl fun x _ => ?_]
      · rw [Finset.sum_const, Finset.card_eq_sum_ones]
        · norm_num
          rw [mul_comm]
      · simp +zetaDelta at *
        rw [show { x_1 ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A) |
            ∃ a ∈ A, a + x = x_1 } = Finset.image (fun a => a + x) A from ?_]
        · exact Finset.card_image_of_injective _ (add_left_injective x)
        · ext; aesop
    have h_sum_r_sq :
        (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
          (fun j => Finset.image (fun a => a + j) A),
          ((∑ j ∈ Finset.Icc 1 m,
            (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2) ≤
        (A.card * m : ℝ) + (m * (m - 1)) := by
      have h_sum_bound :
          ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
            (fun j => Finset.image (fun a => a + j) A),
            ((∑ j ∈ Finset.Icc 1 m,
              (if ∃ a ∈ A, a + j = x then 1 else 0)) : ℝ) ^ 2 ≤
          ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
            (if j = j' then (A.card : ℝ) else 1) := by
        have h_pair_bound : ∀ j j' : ℕ, j ∈ Finset.Icc 1 m → j' ∈ Finset.Icc 1 m →
            (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (if ∃ a ∈ A, a + j = x then 1 else 0) *
              (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
            if j = j' then (A.card : ℝ) else 1 := by
          intros j j' hj hj'
          have h_le_filter :
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) ≤
              (Finset.filter (fun x => ∃ a ∈ A, a + j = x ∧ ∃ a ∈ A, a + j' = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A))).card := by
            rw [Finset.card_filter]
            push_cast [Finset.sum_mul _ _ _]
            gcongr; aesop
          split_ifs
          · simp_all
            exact le_trans (Finset.card_le_card
              (show Finset.filter (fun x => ∃ a ∈ A, a + j' = x)
                (Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A)) ⊆
                Finset.image (fun a => a + j') A from fun x hx => by aesop))
              Finset.card_image_le
          · refine le_trans h_le_filter ?_
            have h_unique : ∀ x y : ℕ,
                x ∈ Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A) →
                y ∈ Finset.biUnion (Finset.Icc 1 m)
                  (fun j => Finset.image (fun a => a + j) A) →
                (∃ a ∈ A, a + j = x ∧ ∃ a ∈ A, a + j' = x) →
                (∃ a ∈ A, a + j = y ∧ ∃ a ∈ A, a + j' = y) → x = y := by
              intros x y _ _ hx' hy'
              obtain ⟨a, haA, ha_eq_x, b, hbA, hb_eq_x⟩ := hx'
              obtain ⟨c, hcA, hc_eq_y, d, hdA, hd_eq_y⟩ := hy'
              have := hSidon a d b c haA hdA hbA hcA
              simp_all [add_comm]; grind
            exact_mod_cast Finset.card_le_one.mpr fun x hx y hy =>
              h_unique x y (Finset.mem_filter.mp hx |>.1)
                (Finset.mem_filter.mp hy |>.1)
                (Finset.mem_filter.mp hx |>.2) (Finset.mem_filter.mp hy |>.2)
        have h_expand :
            ∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
              (fun j => Finset.image (fun a => a + j) A),
              (∑ j ∈ Finset.Icc 1 m,
                (if ∃ a ∈ A, a + j = x then 1 else 0) : ℝ) ^ 2 =
            ∑ j ∈ Finset.Icc 1 m, ∑ j' ∈ Finset.Icc 1 m,
              (∑ x ∈ Finset.biUnion (Finset.Icc 1 m)
                (fun j => Finset.image (fun a => a + j) A),
                (if ∃ a ∈ A, a + j = x then 1 else 0) *
                (if ∃ a ∈ A, a + j' = x then 1 else 0) : ℝ) := by
          simp +decide only [pow_two, Finset.sum_mul _ _ _]
          rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm]
          simp +decide only [Finset.mul_sum _ _ _]
        exact h_expand.symm ▸ Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun j hj => by aesop
      simp_all [Finset.sum_ite, Finset.filter_eq, Finset.filter_ne]; linarith
    exact h_cs_inner.trans (mul_le_mul_of_nonneg_left h_sum_r_sq <|
      Nat.cast_nonneg _)
  have h_support_size :
      (Finset.card (Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A))) ≤ (N + m - 1 : ℝ) := by
    norm_cast
    rw [Int.subNatNat_of_le (by omega)]; norm_cast
    exact le_trans (Finset.card_le_card
      (show Finset.biUnion (Finset.Icc 1 m)
        (fun j => Finset.image (fun a => a + j) A) ⊆ Finset.Icc 2 (N + m) from
        Finset.biUnion_subset.2 fun j hj =>
          Finset.image_subset_iff.2 fun a ha =>
            Finset.mem_Icc.2 ⟨by
              have := Finset.mem_Icc.1 (hA ha)
              have := Finset.mem_Icc.1 hj
              omega, by
              have := Finset.mem_Icc.1 (hA ha)
              have := Finset.mem_Icc.1 hj
              omega⟩)) (by norm_num; omega)
  have h_sub : ((Finset.card A * m : ℝ)) ^ 2 ≤
      ((N + m - 1 : ℝ)) * ((Finset.card A * m : ℝ) + (m * (m - 1))) :=
    h_cauchy_schwarz.trans (mul_le_mul_of_nonneg_right h_support_size <|
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) <| Nat.cast_nonneg _) <|
      mul_nonneg (Nat.cast_nonneg _) <| sub_nonneg.mpr <|
      Nat.one_le_cast.mpr hm)
  field_simp at *
  nlinarith [show (m : ℝ) ≥ 1 by norm_cast]

/-
Algebraic bound for x satisfying a quadratic inequality x ^ 2 ≤ bx + c.
-/
lemma quadratic_bound_pos {x b c : ℝ} (c_nonneg : 0 ≤ c) (h : x ^ 2 ≤ b * x + c) :
    x ≤ (b + Real.sqrt (b ^ 2 + 4 * c)) / 2 := by
      nlinarith [
        Real.sqrt_nonneg (b ^ 2 + 4 * c),
        Real.mul_self_sqrt (by positivity : 0 ≤ b ^ 2 + 4 * c)
      ]

/-
Limit lemma for Erdős-Turán (sequence version).
-/
lemma erdos_turan_limit_lemma_nat {m : ℕ → ℝ} (hm_pos : ∀ᶠ n in atTop, 0 < m n)
    (hm1 : Tendsto (fun (n : ℕ) => m n / (n : ℝ)) atTop (nhds 0))
    (hm2 : Tendsto (fun (n : ℕ) => Real.sqrt (n : ℝ) / m n) atTop (nhds 0)) :
    Tendsto
      (fun (n : ℕ) =>
        (((n : ℝ) + m n) / (m n) +
          Real.sqrt ((((n : ℝ) + m n) / (m n)) ^ 2 + 4 * ((n : ℝ) + m n))) /
            (2 * Real.sqrt (n : ℝ)))
      atTop (nhds 1) := by
      -- Let's simplify the expression inside the limit.
      suffices h_simp :
          Filter.Tendsto
            (fun n : ℕ =>
              ((Real.sqrt n / m n + 1 / Real.sqrt n) +
                Real.sqrt
                  ((Real.sqrt n / m n + 1 / Real.sqrt n) ^ 2 +
                    4 * (1 + m n / n))) / 2)
            Filter.atTop (nhds 1) by
        refine h_simp.congr' ?_;
        filter_upwards [ hm_pos, Filter.eventually_gt_atTop 0 ] with n hn hn';
        field_simp [hn, hn']
        ring_nf;
        norm_num [
          show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring,
          hn.ne', hn'.ne', mul_assoc, mul_comm, mul_left_comm
        ]
        ring_nf;
        field_simp;
        rw [
          show
              (m n * ((m n * 4 + 2) * n + m n ^ 2 * 4) + n ^ 2 + m n ^ 2 : ℝ) /
                  (m n ^ 2 * n) =
                ((m n * (m n + 2 * n + m n ^ 2 * 4) + n ^ 2 + m n ^ 2 * 4 * n) /
                    m n ^ 2) / n by
            rw [div_div]
            ring
        ]
        norm_num [hn.ne', hn'.ne']
        ring_nf;
        exact mul_div_cancel_left₀ _ <| ne_of_gt <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hn';
      convert
        Filter.Tendsto.div_const
          (Filter.Tendsto.add
            (hm2.add (tendsto_inv_atTop_nhds_zero_nat.sqrt))
            (Filter.Tendsto.sqrt
              (Filter.Tendsto.add
                (Filter.Tendsto.pow
                  (hm2.add (tendsto_inv_atTop_nhds_zero_nat.sqrt)) 2)
                (tendsto_const_nhds.mul (tendsto_const_nhds.add hm1)))))
          2 using 2
      all_goals norm_num
      all_goals try congr! 1
      all_goals norm_num

/-
Explicit algebraic bound for the size of a Sidon set using the Erdős-Turán inequality.
-/
lemma erdos_turan_explicit_bound {N m : ℕ} (hm : 0 < m) (A : Finset ℕ)
    (hSidon : Sidon (A : Set ℕ)) (hA : A ⊆ Finset.Icc 1 N) :
    (A.card : ℝ) ≤
      ((N + m : ℝ) / m +
        Real.sqrt (((N + m : ℝ) / m) ^ 2 + 4 * (N + m))) / 2 := by
      have := @erdos_turan_inequality N m hm A hSidon hA;
      convert quadratic_bound_pos ?_ ?_ using 1;
      · positivity;
      · convert this using 1 ; ring

/- Erdős-Turán Theorem: f(N) ≤ (1+ε)√N for large N. -/
theorem ErdosTuran : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (f N : ℝ) ≤ (1 + ε) * Real.sqrt N := by
  intro ε hε_pos
  obtain ⟨N0, hN0⟩ :
      ∃ N0 : ℕ, ∀ N ≥ N0,
        ((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) /
            Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) +
          Real.sqrt
            (((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) /
                Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 +
              4 * (N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))))) /
            (2 * Real.sqrt N) <
          1 + ε := by
    have h_limit :
        Filter.Tendsto
          (fun N : ℕ =>
            ((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) /
                Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) +
              Real.sqrt
                (((N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) /
                    Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))) ^ 2 +
                  4 * (N + Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ))))) /
                (2 * Real.sqrt N))
          Filter.atTop (nhds 1) := by
      have h_m_pos : ∀ᶠ N in Filter.atTop, 0 < Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) := by
        filter_upwards [Filter.eventually_gt_atTop 1] with N hN using
          Nat.floor_pos.mpr (Real.one_le_rpow hN.le (by norm_num))
      have h_m1 :
          Filter.Tendsto
            (fun N : ℕ => (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ) / N)
            Filter.atTop (nhds 0) := by
        -- We'll use the fact that $⌊(N : ℝ) ^ (3 / 4 : ℝ)⌋₊ \leq (N : ℝ) ^ (3 / 4 : ℝ)$
        -- and $(N : ℝ) ^ (3 / 4 : ℝ) / N = N^{-1/4}$.
        have h_floor_le :
            ∀ N : ℕ,
              (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ) / N ≤
                (N : ℝ) ^ (-1 / 4 : ℝ) := by
          intro N; by_cases hN : N = 0 <;> norm_num [ hN ];
          rw [ div_le_iff₀ ( by positivity ) ];
          exact
            le_trans (Nat.floor_le (by positivity))
              (by
                rw [← Real.rpow_add_one (by positivity)]
                norm_num)
        exact
          squeeze_zero (fun N => by positivity) h_floor_le
            (by
              simpa [neg_div, Function.comp_def] using
                (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
      have h_m2 :
          Filter.Tendsto
            (fun N : ℕ =>
              Real.sqrt N / (Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) : ℝ))
            Filter.atTop (nhds 0) := by
        -- We'll use the fact that $\sqrt{N} / \lfloor N^{3/4} \rfloor \leq
        -- \sqrt{N} / (N^{3/4} - 1)$.
        suffices h_sqrt_div_floor_le :
            Filter.Tendsto
              (fun N : ℕ => Real.sqrt (N : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1))
              Filter.atTop (nhds 0) by
          refine squeeze_zero_norm' ?_ h_sqrt_div_floor_le;
          filter_upwards [Filter.eventually_gt_atTop 1] with n hn using by
            rw [Real.norm_of_nonneg (by positivity)]
            exact
              div_le_div_of_nonneg_left (by positivity)
                (sub_pos.mpr <| Real.one_lt_rpow (by norm_cast) <| by norm_num)
                (by
                  linarith [Nat.lt_floor_add_one ((n : ℝ) ^ (3 / 4 : ℝ))])
        -- We can simplify the expression inside the limit.
        suffices h_simplify :
            Filter.Tendsto
              (fun N : ℕ =>
                (N : ℝ) ^ (1 / 2 : ℝ) / ((N : ℝ) ^ (3 / 4 : ℝ) - 1))
              Filter.atTop (nhds 0) by
          simpa only [ Real.sqrt_eq_rpow ] using h_simplify;
        -- We can divide the numerator and the denominator by $N^{3/4}$.
        suffices h_div :
            Filter.Tendsto
              (fun N : ℕ =>
                (N : ℝ) ^ (1 / 2 - 3 / 4 : ℝ) /
                  (1 - 1 / (N : ℝ) ^ (3 / 4 : ℝ)))
              Filter.atTop (nhds 0) by
          refine h_div.congr' ?_;
          filter_upwards [Filter.eventually_gt_atTop 0] with N hN using by
            rw [one_sub_div (by positivity)]
            rw [div_div_eq_mul_div]
            rw [← Real.rpow_add (by positivity)]
            ring_nf;
        norm_num [ Real.rpow_neg ];
        exact
          le_trans
            (Filter.Tendsto.div
              (tendsto_inv_atTop_zero.comp
                ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop))
              (tendsto_const_nhds.sub <|
                tendsto_inv_atTop_zero.comp
                  ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop))
              (by norm_num))
            (by norm_num)
      convert erdos_turan_limit_lemma_nat _ _ _ using 2;
      · filter_upwards [Filter.eventually_gt_atTop 0] with N hN using
          Nat.cast_pos.mpr <| Nat.floor_pos.mpr <|
            Real.one_le_rpow (mod_cast hN) <| by norm_num
      · convert h_m1 using 1;
      · convert h_m2 using 1;
    simpa using h_limit.eventually ( gt_mem_nhds <| by linarith );
  use N0 + 1;
  -- By definition of $f$, we know that $f(N)$ is the maximum size of a Sidon
  -- subset of $[1, N]$.
  intro N hN
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Sidon (A : Set ℕ) ∧ A.card = f N := by
    -- Hence, there exists a Sidon subset $A$ of $[1, N]$ with $|A| = f(N)$.
    obtain ⟨A, hA⟩ :
        ∃ A : Finset ℕ,
          A ⊆ Finset.Icc 1 N ∧ Sidon (A : Set ℕ) ∧
            ∀ B : Finset ℕ,
              B ⊆ Finset.Icc 1 N → Sidon (B : Set ℕ) → B.card ≤ A.card := by
      have h_finite :
          Set.Finite {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)} := by
        exact
          Set.finite_iff_bddAbove.mpr
            ⟨Finset.Icc 1 N, fun B hB => hB.1⟩;
      have h_max :
          ∃ A ∈ {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)},
            ∀ B ∈ {B : Finset ℕ | B ⊆ Finset.Icc 1 N ∧ Sidon (B : Set ℕ)},
              A.card ≥ B.card := by
        apply_rules [ Set.exists_max_image ];
        exact ⟨ ∅, by simp +decide [ Sidon ] ⟩;
      exact
        ⟨h_max.choose, h_max.choose_spec.1.1, h_max.choose_spec.1.2,
          fun B hB₁ hB₂ => h_max.choose_spec.2 B ⟨hB₁, hB₂⟩⟩;
    refine ⟨ A, hA.1, hA.2.1, le_antisymm ?_ ?_ ⟩;
    · refine Finset.le_sup ( f := Finset.card ) ?_;
      aesop;
    · exact Finset.sup_le fun B hB => by aesop;
  have :=
    erdos_turan_explicit_bound
      (show 0 < Nat.floor ((N : ℝ) ^ (3 / 4 : ℝ)) from
        Nat.floor_pos.mpr <| Real.one_le_rpow (mod_cast by linarith) <| by norm_num)
      A hA.2.1 hA.1;
  have := hN0 N (by linarith)
  rw [
    div_lt_iff₀
      (mul_pos zero_lt_two <| Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by linarith)
  ] at this
  nlinarith [
    Real.sqrt_nonneg N,
    Real.sq_sqrt <| Nat.cast_nonneg N,
    show (A.card : ℝ) = f N from mod_cast hA.2.2
  ]

end ErdosTuran

/-!
## Bose-Chowla Theorem

**Theorem (Bose-Chowla, 1962):** For any prime power $q$, there exists a set
$S \subseteq \{1, 2, \ldots, q^2 - 2\}$ of size $|S| = q$ that is Sidon modulo $q^2 - 1$.

**Construction:** We follow the proof in Nathanson (2021).
Let $\mathbb{F}_q$ be the finite field of order $q$, and let $\mathbb{F}_{q^2}$ be
its quadratic extension. Let $\theta \in \mathbb{F}_{q^2}$ be a primitive
$(q^2 - 1)$-th root of unity. For each $x \in \mathbb{F}_q$, there exists a unique
$k_x \in \{1, 2, \ldots, q^2 - 2\}$ such that $\theta^{k_x} = \theta - x$.
The set $S = \{k_x : x \in \mathbb{F}_q\}$ is Sidon modulo $q^2 - 1$.

**Key ideas:**
- $\theta \notin \mathbb{F}_q$ (since $\theta$ is a primitive $(q^2-1)$-th root but $q^2-1$
  does not divide $q-1$).
- The map $x \mapsto k_x$ is well-defined and injective.
- The polynomial identity argument shows that distinct $h$-fold sums from $S$ yield distinct
  products of roots in $\mathbb{F}_{q^2}$, establishing the Sidon property modulo $q^2 - 1$.
-/

section BoseChowla

variable {Fq Fqh : Type*} [Field Fq] [Fintype Fq]

variable [Field Fqh] [Fintype Fqh]

variable [Algebra Fq Fqh]

/-- The modulus q^h - 1 in the Bose–Chowla theorem. -/
def boseChowlaMod (h : ℕ) : ℕ := (Fintype.card Fq) ^ h - 1

omit [Fintype Fqh] in
theorem theta_not_in_Fq {h : ℕ} (hh : 2 ≤ h) (_hdeg : Module.finrank Fq Fqh = h)
    (theta : Fqh) (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∀ x : Fq, theta ≠ algebraMap Fq Fqh x := by
  unfold boseChowlaMod at htheta
  intro x hx
  have := htheta.pow_eq_one
  rw [hx] at this
  have := htheta.2
  simp_all [IsPrimitiveRoot.iff_def]
  contrapose! this
  refine ⟨Fintype.card Fq - 1, ?_, ?_⟩
  · by_cases hx0 : x = 0
    · simp_all [Nat.sub_ne_zero_of_lt (Fintype.one_lt_card)]
      rw [zero_pow (Nat.sub_ne_zero_of_lt
        (one_lt_pow₀ (Fintype.one_lt_card) (by linarith)))] at this
      simp_all
    · rw [← map_pow, FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  · refine Nat.not_dvd_of_pos_of_lt ?_ ?_
    · exact Nat.sub_pos_of_lt (Fintype.one_lt_card)
    · rw [tsub_lt_tsub_iff_right
        (Nat.one_le_iff_ne_zero.mpr <| Fintype.card_ne_zero)]
      exact lt_self_pow₀ (Fintype.one_lt_card) hh

omit [Fintype Fqh] in
theorem bose_chowla_exponents {h : ℕ} [Finite Fqh] (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∀ x : Fq, ∃! k : ℕ, 0 < k ∧ k < boseChowlaMod (Fq := Fq) h ∧
      theta ^ k = theta - algebraMap Fq Fqh x := by
  let := Fintype.ofFinite Fqh
  intro x
  have h_neq : theta ≠ algebraMap Fq Fqh x :=
    theta_not_in_Fq hh hdeg theta htheta x
  have h_sub_neq_zero : theta - algebraMap Fq Fqh x ≠ 0 := sub_ne_zero.mpr h_neq
  have h_card : Fintype.card Fqh = Fintype.card Fq ^ h := by
    rw [← hdeg]; exact Module.card_eq_pow_finrank (K := Fq) (V := Fqh)
  have h_mod : boseChowlaMod (Fq := Fq) h = Fintype.card Fqh - 1 := by
    unfold boseChowlaMod; rw [h_card]
  rw [h_mod] at htheta ⊢
  have h_order : ∀ y : Fqh, y ≠ 0 →
      ∃ k : ℕ, 0 ≤ k ∧ k < Fintype.card Fqh - 1 ∧ theta ^ k = y := by
    intro y hy_ne_zero
    have h_ord : y ∈ Set.range (fun k : ℕ => theta ^ k) := by
      have h_cyclic : ∀ y : Fqhˣ,
          y ∈ Subgroup.zpowers (Units.mk0 theta (by
            intro hzero; simp_all [IsPrimitiveRoot.iff_def]
            have hpos : 0 < Fintype.card Fq ^ h - 1 := Nat.sub_pos_of_lt
              (one_lt_pow₀ (Fintype.one_lt_card) (by linarith))
            simp [zero_pow hpos.ne'] at htheta)) := by
        generalize_proofs at *
        have h_gen : Subgroup.zpowers (Units.mk0 theta (by aesop)) = ⊤ := by
          refine Subgroup.eq_top_of_card_eq _ ?_
          rw [Nat.card_zpowers, orderOf_eq_iff]
          · simp_all [Units.ext_iff]
            intro m hm₁ hm₂ hm₃
            have := htheta.pow_eq_one_iff_dvd m
            simp_all
            exact hm₁.not_ge (Nat.le_of_dvd hm₂
              (by simpa [Nat.card_eq_fintype_card, h_card, Nat.card_units]
                using hm₃))
          · simp +decide
        generalize_proofs at *; aesop
      obtain ⟨k, hk⟩ := h_cyclic (Units.mk0 y hy_ne_zero)
      rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩ <;>
        simp_all [Units.ext_iff]
      · use k
      · use (Fintype.card Fqh - 1) - k % (Fintype.card Fqh - 1)
        rw [← hk, ← Nat.mod_add_div k (Fintype.card Fqh - 1)]
        have h_ord' : theta ^ (Fintype.card Fqh - 1) = 1 := by
          have := htheta.pow_eq_one; aesop
        simp +decide [pow_add, pow_mul, h_ord']
        exact eq_inv_of_mul_eq_one_left (by
          rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt
            (Nat.mod_lt _ (Nat.sub_pos_of_lt Fintype.one_lt_card))), h_ord'])
    simp +zetaDelta at *
    obtain ⟨k, rfl⟩ := h_ord
    exact ⟨k % (Fintype.card Fqh - 1),
      Nat.mod_lt _ (Nat.sub_pos_of_lt (Fintype.one_lt_card)), by
        rw [← Nat.mod_add_div k (Fintype.card Fqh - 1), pow_add, pow_mul]
        simp +decide [htheta.pow_eq_one]⟩
  obtain ⟨k, _, hk₂, hk₃⟩ := h_order _ h_sub_neq_zero
  refine ⟨k, ⟨Nat.pos_of_ne_zero ?_, hk₂, hk₃⟩, fun m ⟨hm₁, hm₂, hm₃⟩ => ?_⟩
  · rintro rfl; simp_all
    have := theta_not_in_Fq hh hdeg theta htheta
    simp_all
    exact this (x + 1) (by simpa using eq_add_of_sub_eq' hk₃.symm)
  · have := htheta.pow_inj (by linarith : m < Fintype.card Fqh - 1)
      (by linarith : k < Fintype.card Fqh - 1)
    aesop

omit [Fintype Fqh] in
theorem minpoly_degree_eq_h {h : ℕ} [Finite Fqh] (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    (minpoly Fq theta).natDegree = h := by
  let := Fintype.ofFinite Fqh
  have h_subfield : (IntermediateField.adjoin Fq {theta}) = ⊤ := by
    have h_pow : ∀ x : Fqh, x ≠ 0 → ∃ k : ℕ, x = theta ^ k := by
      intro x hx_ne_zero
      have h_ord : IsPrimitiveRoot theta (Fintype.card Fqh - 1) := by
        have h_card : Fintype.card Fqh = (Fintype.card Fq) ^ h := by
          have := Module.card_eq_pow_finrank (K := Fq) (V := Fqh)
          rw [this, hdeg]
        aesop
      have h_inner : ∀ x : Fqh, x ≠ 0 → ∃ k : ℕ, x = theta ^ k := by
        intro x hx_ne
        have h_units : ∀ y : Fqhˣ, ∃ k : ℕ, y = theta ^ k := by
          intro y
          have h_mem : y ∈ Subgroup.zpowers (Units.mk0 theta
              (h_ord.ne_zero (Nat.sub_ne_zero_of_lt (Fintype.one_lt_card)))) := by
            generalize_proofs at *
            have h_top : Subgroup.zpowers (Units.mk0 theta ‹_›) = ⊤ := by
              refine Subgroup.eq_top_of_card_eq _ ?_
              simp +zetaDelta at *
              rw [orderOf_eq_iff]
              · simp_all +decide [Units.ext_iff, IsPrimitiveRoot.iff_def]
                intro m hm₁ hm₂ hm₃
                have := h_ord.2 m hm₃
                rw [Nat.dvd_iff_mod_eq_zero] at this
                rw [Nat.mod_eq_of_lt] at this <;>
                  simp_all +decide
                rw [Nat.card_units] at hm₁; aesop
              · simp +decide
            aesop
          generalize_proofs at *
          obtain ⟨k, hk⟩ := h_mem
          rw [← hk]
          rcases Int.eq_nat_or_neg k with ⟨k, rfl | rfl⟩ <;> norm_num
          use (Fintype.card Fqh - 1) - k % (Fintype.card Fqh - 1)
          rw [inv_eq_of_mul_eq_one_right]
          rw [← pow_add, ← Nat.mod_add_div k (Fintype.card Fqh - 1), add_comm]
          simp +decide
          rw [show Fintype.card Fqh - 1 - k % (Fintype.card Fqh - 1) +
              (k % (Fintype.card Fqh - 1) +
                (Fintype.card Fqh - 1) * (k / (Fintype.card Fqh - 1))) =
              (Fintype.card Fqh - 1) * (k / (Fintype.card Fqh - 1) + 1) by
            linarith [Nat.sub_add_cancel (show k % (Fintype.card Fqh - 1) ≤
              Fintype.card Fqh - 1 from Nat.le_of_lt (Nat.mod_lt _
                (Nat.sub_pos_of_lt (Fintype.one_lt_card))))]]
          simp +decide [pow_mul, h_ord.pow_eq_one]
        simpa using h_units (Units.mk0 x hx_ne)
      exact h_inner x hx_ne_zero
    ext x
    by_cases hx : x = 0 <;>
      simp_all +decide [IntermediateField.mem_adjoin_simple_iff]
    obtain ⟨k, rfl⟩ := h_pow x hx
    exact ⟨Polynomial.X ^ k, 1, by simp +decide⟩
  have := IntermediateField.adjoin.finrank
    (show IsIntegral Fq theta from Algebra.IsIntegral.isIntegral theta)
  · rw [← this, ← hdeg, h_subfield]; simp +decide

theorem multiset_prod_X_sub_C_injective {F : Type*} [Field F] (s t : Multiset F) :
    (s.map (fun x => Polynomial.X - Polynomial.C x)).prod =
    (t.map (fun x => Polynomial.X - Polynomial.C x)).prod ↔ s = t := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  replace h := congr_arg (fun p => Polynomial.roots p) h
  simp_all +decide

omit [Fintype Fqh] in
theorem bose_chowla_poly_identity {h : ℕ} [Finite Fqh] (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h))
    (s t : Multiset Fq) (hs : s.card = h) (ht : t.card = h)
    (heq : (s.map (fun x => theta - algebraMap Fq Fqh x)).prod =
           (t.map (fun x => theta - algebraMap Fq Fqh x)).prod) :
    s = t := by
  let := Fintype.ofFinite Fqh
  set Ps : Polynomial Fq :=
    Multiset.prod (Multiset.map (fun x => Polynomial.X - Polynomial.C x) s)
  set Pt : Polynomial Fq :=
    Multiset.prod (Multiset.map (fun x => Polynomial.X - Polynomial.C x) t)
  set Q : Polynomial Fq := Ps - Pt
  have hQ : Polynomial.aeval theta Q = 0 := by
    simp +zetaDelta at *
    simp_all +decide [Polynomial.aeval_def, Polynomial.eval₂_multiset_prod]
  have hQ_zero : Q = 0 := by
    have hQ_div_minpoly : minpoly Fq theta ∣ Q := minpoly.dvd Fq theta hQ
    have hQ_deg : Q.degree < h := by
      refine lt_of_lt_of_le (Polynomial.degree_sub_lt_left ?_ ?_ ?_) ?_
      · rw [Polynomial.degree_multiset_prod, Polynomial.degree_multiset_prod]
        aesop
      · simp +zetaDelta at *
        exact fun x hx => Polynomial.X_sub_C_ne_zero x
      · rw [Polynomial.leadingCoeff_multiset_prod,
          Polynomial.leadingCoeff_multiset_prod]
        aesop
      · erw [Polynomial.degree_multiset_prod]; aesop
    have hQ_minpoly_deg : (minpoly Fq theta).degree = h := by
      convert minpoly_degree_eq_h hh hdeg theta htheta
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero
        (show IsIntegral Fq theta from IsIntegral.of_finite Fq theta))]
      norm_cast
    contrapose! hQ_deg
    exact hQ_minpoly_deg ▸ Polynomial.degree_le_of_dvd hQ_div_minpoly hQ_deg
  apply (multiset_prod_X_sub_C_injective s t).mp
  exact eq_of_sub_eq_zero hQ_zero

omit [Fintype Fqh] in
theorem bose_chowla {h : ℕ} [Finite Fqh] (hh : 2 ≤ h)
    (hdeg : Module.finrank Fq Fqh = h) (theta : Fqh)
    (htheta : IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) h)) :
    ∃ a : Fq → {k : ℕ // 0 < k ∧ k < boseChowlaMod (Fq := Fq) h},
      (∀ x : Fq, theta ^ (a x).1 = theta - algebraMap Fq Fqh x) ∧
      (∀ x : Fq, ∀ e : {k : ℕ // 0 < k ∧ k < boseChowlaMod (Fq := Fq) h},
        theta ^ e.1 = theta - algebraMap Fq Fqh x → e = a x) ∧
      (let A : Finset ℕ := Finset.univ.image (fun x : Fq => (a x).1)
       SidonModOfOrder h (boseChowlaMod (Fq := Fq) h) (A : Set ℕ) ∧
          A.card = Fintype.card Fq) := by
  classical
  let := Fintype.ofFinite Fqh
  -- Abbreviation for the repeated exponents call
  let BC := bose_chowla_exponents hh hdeg theta htheta
  let k := fun x : Fq => (BC x).exists.choose
  have hk₁ := fun x => (BC x).exists.choose_spec.1
  have hk₂ := fun x => (BC x).exists.choose_spec.2.1
  have hk₃ := fun x => (BC x).exists.choose_spec.2.2
  refine ⟨fun x => ⟨k x, hk₁ x, hk₂ x⟩,
          fun x => hk₃ x,
          fun x e he => Subtype.ext (ExistsUnique.unique (BC x) ⟨e.2.1, e.2.2, he⟩
            (ExistsUnique.exists (BC x) |> Classical.choose_spec)),
          ?_, ?_⟩
  · intro u v hu hv heq
    obtain ⟨xu, hxu⟩ : ∃ x : Fin h → Fq, ∀ i, u i = k (x i) := by
      choose x hx using hu
      choose g hg using fun i => Finset.mem_image.mp (hx i |>.1)
      exact ⟨g, fun i => hx i |>.2.symm.trans (congr_arg _ (hg i |>.2.symm))⟩
    obtain ⟨xv, hxv⟩ : ∃ y : Fin h → Fq, ∀ i, v i = k (y i) := by
      choose y hy using hv
      choose g hg using fun i => Finset.mem_image.mp (hy i |>.1)
      exact ⟨g, fun i => hy i |>.2.symm.trans (congr_arg _ (hg i |>.2.symm))⟩
    have h_prod_eq :
        (Finset.univ.prod (fun i => theta - algebraMap Fq Fqh (xu i))) =
        (Finset.univ.prod (fun i => theta - algebraMap Fq Fqh (xv i))) := by
      have h_pow_prod :
          (Finset.univ.prod (fun i => theta ^ (BC (xu i)).exists.choose)) =
          (Finset.univ.prod (fun i => theta ^ (BC (xv i)).exists.choose)) := by
        have h_pow_sum :
            (∏ i, theta ^ (BC (xu i)).exists.choose) =
            theta ^ (∑ i, (BC (xu i)).exists.choose) ∧
            (∏ i, theta ^ (BC (xv i)).exists.choose) =
            theta ^ (∑ i, (BC (xv i)).exists.choose) :=
          ⟨by rw [Finset.prod_pow_eq_pow_sum], by rw [Finset.prod_pow_eq_pow_sum]⟩
        simp_all +decide
        norm_cast at *
        rw [ZMod.natCast_eq_natCast_iff] at heq
        rw [← Nat.mod_add_div (∑ i, _) _, ← Nat.mod_add_div (∑ i, _) _, heq]
        · rw [← Nat.mod_add_div (∑ i, _) _]
          · simp +decide [pow_add, pow_mul]
            rw [htheta.pow_eq_one]; norm_num
      convert h_pow_prod using 2 <;>
        have := (BC (xu ‹_›)).exists.choose_spec <;>
        have := (BC (xv ‹_›)).exists.choose_spec <;>
        aesop
    have h_multiset_eq := bose_chowla_poly_identity hh hdeg theta htheta
      (Multiset.ofList (List.ofFn xu)) (Multiset.ofList (List.ofFn xv))
      (by simp +decide) (by simp +decide) (by simp_all +decide [List.prod_ofFn])
    have h_multiset_exp : Multiset.ofList (List.ofFn (fun i => k (xu i))) =
        Multiset.ofList (List.ofFn (fun i => k (xv i))) := by
      convert congr_arg (Multiset.map (fun x : Fq => k x)) h_multiset_eq using 1 <;>
        simp +decide [List.ofFn_eq_map] <;>
        exact List.Perm.map _ (List.Perm.symm <| List.perm_of_nodup_nodup_toFinset_eq
          (List.nodup_finRange _) (List.nodup_finRange _) <| by simp)
    simp_all +decide [List.ofFn_eq_map]
    convert h_multiset_exp.map (fun x : ℕ => (x : ZMod (boseChowlaMod h))) using 1 <;>
      simp +decide [hxu, hxv]
  · rw [Finset.card_image_of_injective _ fun x y hxy => ?_, Finset.card_univ]
    have := hk₃ x; have := hk₃ y; aesop

/-- Sidon of order 2 is equivalent to the standard Sidon definition. -/
lemma SidonOfOrder_two_iff_Sidon {α : Type} [AddCommMonoid α] (S : Set α) :
    SidonOfOrder 2 S ↔ Sidon S := by
  constructor
  · intro h x y z w hx hy hz hw hsum
    specialize h (fun i => if i = 0 then x else y)
      (fun i => if i = 0 then z else w)
    simp_all +decide
    ext a; simpa using h.mem_iff
  · intro h_Sidon u v hu hv h_eq_sum
    have h_eq_set : ({(u 0), (u 1)} : Set α) = ({(v 0), (v 1)} : Set α) :=
      h_Sidon _ _ _ _ (hu 0) (hu 1) (hv 0) (hv 1)
        (by simpa [add_comm] using h_eq_sum)
    simp_all +decide [Set.Subset.antisymm_iff, Set.subset_def]
    rcases h_eq_set with ⟨⟨h₀ | h₀, h₁ | h₁⟩, _, _⟩ <;>
      simp_all +decide [List.Perm.swap]

/-- There exists an irreducible polynomial of degree 2 over any finite field. -/
lemma exists_irreducible_poly_of_degree_two {F : Type*} [Field F] [Finite F] :
    ∃ f : Polynomial F, Polynomial.natDegree f = 2 ∧ Irreducible f := by
  let := Fintype.ofFinite F
  set q := Fintype.card F with hq_def
  have h_card : 2 ≤ q := Fintype.one_lt_card
  have h_exists_a : ∃ a : F, ¬∃ x : F, x ^ 2 - x = a := by
    by_contra h_contra
    push Not at h_contra
    have h_surj : Function.Surjective (fun x : F => x ^ 2 - x) := fun x => h_contra x
    have h_inj : Function.Injective (fun x : F => x ^ 2 - x) :=
      Finite.injective_iff_surjective.mpr h_surj
    have := @h_inj 0 1; simp_all +decide
  obtain ⟨a, ha⟩ : ∃ a : F, ¬∃ x : F, x ^ 2 - x = a := h_exists_a
  use Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a
  rw [Polynomial.natDegree_sub_C,
    Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> norm_num
  have h_no_roots :
      ¬∃ x : F, Polynomial.eval x
        (Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a) = 0 := by
    simp_all +decide [sub_eq_iff_eq_add]
  have h_irred : ∀ p q : Polynomial F, p.degree > 0 → q.degree > 0 →
      Polynomial.X ^ 2 - Polynomial.X - Polynomial.C a = p * q → False := by
    intros p q hp hq h_factor
    have h_deg : p.degree + q.degree = 2 := by
      rw [← Polynomial.degree_mul, ← h_factor, Polynomial.degree_sub_C] <;>
        rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num
    have h_linear : p.degree = 1 ∧ q.degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hp),
        Polynomial.degree_eq_natDegree (Polynomial.ne_zero_of_degree_gt hq)] at *
      norm_cast at *
      exact ⟨by linarith, by linarith⟩
    exact h_no_roots <| by
      obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one h_linear.1
      exact ⟨x, by aesop⟩
  constructor
  · exact fun h => absurd (Polynomial.degree_eq_zero_of_isUnit h) (by
      erw [Polynomial.degree_sub_C] <;>
        erw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> norm_num)
  · contrapose! h_irred
    rcases h_irred with ⟨p, q, hpq, hp, hq⟩
    exact ⟨p, q, not_le.mp fun h => hp <|
      Polynomial.isUnit_iff_degree_eq_zero.mpr <| le_antisymm h <|
        le_of_not_gt fun h' => by aesop,
      not_le.mp fun h => hq <| Polynomial.isUnit_iff_degree_eq_zero.mpr <|
        le_antisymm h <| le_of_not_gt fun h' => by aesop, hpq, trivial⟩

/-- For any prime power q, there exists a field extension of degree 2. -/
lemma exists_field_extension_of_degree_two (q : ℕ) (hq : IsPrimePow q) :
    ∃ (Fq Fqh : Type) (_ : Field Fq) (_ : Fintype Fq)
      (_ : Field Fqh) (_ : Fintype Fqh)
      (_ : Algebra Fq Fqh) (_ : FiniteDimensional Fq Fqh),
      Fintype.card Fq = q ∧ Module.finrank Fq Fqh = 2 := by
  -- By definition of prime powers, there exists a finite field Fq with cardinality q.
  obtain ⟨Fq, hFq⟩ : ∃ Fq : Type, ∃ (x : Field Fq) (x_1 : Fintype Fq), Fintype.card Fq = q := by
    obtain ⟨ p, k, hp, hk, rfl ⟩ := hq;
    have := Fact.mk hp.nat_prime;
    -- By definition of finite fields, there exists a finite field Fq with cardinality p^k.
    use (GaloisField p k);
    refine ⟨ ?_, ?_, ?_ ⟩
    · exact inferInstance
    · exact Fintype.ofFinite (GaloisField p k)
    · convert GaloisField.card p k
      simp +decide [ hk.ne', Fintype.card_eq_nat_card ]
  obtain ⟨x, x_1, hx⟩ := hFq;
  -- Let $f(x)$ be an irreducible polynomial of degree 2 over $Fq$.
  obtain ⟨f, hf⟩ : ∃ f : Polynomial Fq, Polynomial.natDegree f = 2 ∧ Irreducible f := by
    exact exists_irreducible_poly_of_degree_two;
  -- Let $Fqh$ be the extension field of $Fq$ obtained by adjoining a root of $f$.
  obtain ⟨Fqh, hFqh⟩ :
      ∃ Fqh : Type,
        ∃ (x_3 : Field Fqh) (x_4 : Fintype Fqh) (x_5 : Algebra Fq Fqh),
          FiniteDimensional Fq Fqh ∧ Module.finrank Fq Fqh = 2 := by
    -- Let $Fqh$ be the extension field of $Fq$ obtained by adjoining a root of
    -- $f$. We can construct $Fqh$ as the quotient ring $Fq[x]/(f(x))$.
    use AdjoinRoot f;
    have := Fact.mk hf.2;
    refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
    all_goals try infer_instance;
    · convert Fintype.ofFinite ( AdjoinRoot f );
      have h_finite : FiniteDimensional Fq (AdjoinRoot f) := by
        exact Module.Basis.finiteDimensional_of_finite ( AdjoinRoot.powerBasis hf.2.ne_zero ).basis;
      have h_finite : Finite (AdjoinRoot f) := by
        have h_finite : FiniteDimensional Fq (AdjoinRoot f) := h_finite
        have h_finite : Finite Fq := by
          infer_instance
        (expose_names; exact Module.finite_iff_finite.mp h_finite_1);
      exact h_finite;
    · exact finite_of_finite_type_of_isJacobsonRing Fq (AdjoinRoot f);
    · rw [
        Module.finrank_eq_card_basis
          (PowerBasis.basis (AdjoinRoot.powerBasis (by aesop)))
      ]
      aesop;
  exact
    ⟨Fq, Fqh, x, x_1, hFqh.choose, hFqh.choose_spec.choose,
      hFqh.choose_spec.choose_spec.choose, hFqh.choose_spec.choose_spec.choose_spec.1,
      hx, hFqh.choose_spec.choose_spec.choose_spec.2⟩

/-- Bose–Chowla for h=2: for prime power q, exists Sidon set of size q in ZMod(q²-1). -/
theorem bose_chowla_at_h_eq_2 : ∀ q : ℕ, IsPrimePow q →
    ∃ S : Finset (ZMod (q ^ 2 - 1)),
      Sidon (S : Set (ZMod (q ^ 2 - 1))) ∧ S.card = q := by
  intro q hq
  obtain ⟨Fq, Fqh, hFq, hFqh, hFintypeFq, hFintypeFqh, hAlgebra, hFiniteDim,
      hcardFq, hfinrankFqh⟩ := exists_field_extension_of_degree_two q hq
  obtain ⟨theta, htheta⟩ : ∃ theta : Fqh,
      IsPrimitiveRoot theta (boseChowlaMod (Fq := Fq) 2) := by
    have h_cyclic : IsCyclic (Fqhˣ) := inferInstance
    obtain ⟨theta, htheta⟩ : ∃ theta : Fqhˣ, orderOf theta = q ^ 2 - 1 := by
      obtain ⟨g, hg⟩ := h_cyclic.exists_generator
      use g
      rw [orderOf_eq_card_of_forall_mem_zpowers hg]
      have h_card : Nat.card Fqh = q ^ 2 := by
        have h_card' : Nat.card Fqh = Nat.card Fq ^ Module.finrank Fq Fqh :=
          Module.natCard_eq_pow_finrank
        aesop
      rw [← h_card, Nat.card_units]
    use theta
    have htheta_unit : IsPrimitiveRoot (theta : Fqhˣ) (Fintype.card Fq ^ 2 - 1) := by
      rw [hcardFq]
      exact htheta ▸ IsPrimitiveRoot.orderOf (theta : Fqhˣ)
    rw [boseChowlaMod]
    rw [IsPrimitiveRoot.iff_def] at htheta_unit ⊢
    exact ⟨
      by
        have := congrArg (fun u : Fqhˣ => (u : Fqh)) htheta_unit.1
        simpa using this,
      fun l hl => htheta_unit.2 l (by
        ext
        simpa using hl)⟩
  have := bose_chowla (by linarith) (by linarith) theta htheta
  obtain ⟨a, ha₁, ha₂, ha₃, ha₄⟩ := this
  refine ⟨Finset.image (fun x : Fq => (a x : ZMod (q ^ 2 - 1))) Finset.univ,
    ?_, ?_⟩
  · convert ha₃ using 1
    rw [← SidonOfOrder_two_iff_Sidon]
    unfold SidonModOfOrder SidonOfOrder; aesop
  · rw [Finset.card_image_of_injective]
    · aesop
    · intro x y hxy
      have h_eq : (a x : ℕ) = (a y : ℕ) := by
        have h_mod : (a x : ℕ) ≡ (a y : ℕ) [MOD (boseChowlaMod (Fq := Fq) 2)] := by
          erw [← ZMod.natCast_eq_natCast_iff]; aesop
        exact Nat.mod_eq_of_lt (a x |>.2.2) ▸
          Nat.mod_eq_of_lt (a y |>.2.2) ▸ h_mod
      have := ha₁ x; aesop

end BoseChowla

section Construction

/-- ZMod equality implies ℕ equality when both values are small. -/
lemma eq_of_zmod_eq_of_lt (M : ℕ) [NeZero M] (a b : ℕ) (ha : a < M) (hb : b < M)
    (h : (a : ZMod M) = (b : ZMod M)) : a = b :=
  (ZMod.val_natCast_of_lt ha).symm.trans ((congrArg ZMod.val h).trans (ZMod.val_natCast_of_lt hb))

/-- ZMod pair equality implies ℕ pair equality when all values are small. -/
lemma set_pair_eq_of_zmod_pair_eq (M : ℕ) [NeZero M] {a b c d : ℕ}
    (ha : a < M) (hb : b < M) (hc : c < M) (hd : d < M)
    (h : ({(a : ZMod M), (b : ZMod M)} : Set (ZMod M)) = {(c : ZMod M), (d : ZMod M)}) :
    ({a, b} : Set ℕ) = {c, d} := by
  rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> apply Set.pair_eq_pair_iff.mpr
  · exact Or.inl ⟨eq_of_zmod_eq_of_lt M a c ha hc h1, eq_of_zmod_eq_of_lt M b d hb hd h2⟩
  · exact Or.inr ⟨eq_of_zmod_eq_of_lt M a d ha hd h1, eq_of_zmod_eq_of_lt M b c hb hc h2⟩

/-- Translate a Sidon set to avoid 0. -/
lemma shift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (hcard : S.card < M) :
    ∃ S' : Finset (ZMod M), Sidon (S' : Set (ZMod M)) ∧
      S'.card = S.card ∧ (0 : ZMod M) ∉ S' := by
  classical
  have : Fact (1 < M) := ⟨hM⟩
  have ⟨x, hx⟩ : ∃ x : ZMod M, x ∉ S := by
    by_contra h; push Not at h
    simp [Finset.eq_univ_iff_forall.mpr h, ZMod.card M] at hcard
  let S' := S.image (· - x)
  have hinj : Function.Injective (fun y : ZMod M => y - x) := sub_left_injective
  refine ⟨S', ?_, Finset.card_image_of_injective S hinj, ?_⟩
  · intro a b c d ha hb hc hd habcd
    have hmem : ∀ z, z ∈ S' → z + x ∈ (S : Set _) := fun z hz => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz; simp [hy]
    have hEq := hS _ _ _ _ (hmem a ha) (hmem b hb) (hmem c hc) (hmem d hd)
      (by linear_combination habcd)
    have h1 : (· - x) '' ({a + x, b + x} : Set _) = {a, b} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    have h2 : (· - x) '' ({c + x, d + x} : Set _) = {c, d} := by
      simp only [Set.image_insert_eq, Set.image_singleton, add_sub_cancel_right]
    rw [← h1, ← h2, Set.image_eq_image hinj]; exact hEq
  · intro h0; obtain ⟨y, hyS, hy0⟩ := Finset.mem_image.1 h0
    exact hx (sub_eq_zero.mp hy0 ▸ hyS)

/-- Lift a Sidon set from ZMod M to naturals. -/
lemma lift_sidon_mod (M : ℕ) (hM : 1 < M) (S : Finset (ZMod M))
    (hS : Sidon (S : Set (ZMod M))) (h0 : (0 : ZMod M) ∉ S) :
    ∃ S_nat : Finset ℕ, SidonMod M (S_nat : Set ℕ) ∧ S_nat.card = S.card ∧
      (S_nat : Set ℕ) ⊆ Finset.Icc 1 (M - 1) ∧ S_nat = S.image ZMod.val := by
  classical
  have : NeZero M := ⟨by linarith⟩
  have hinj : Function.Injective (ZMod.val : ZMod M → ℕ) := ZMod.val_injective M
  refine ⟨S.image ZMod.val, ?_, Finset.card_image_of_injective S hinj, ?_, rfl⟩
  · intro a b c d ha hb hc hd habcd
    obtain ⟨na, hna, rfl⟩ := ha; obtain ⟨nb, hnb, rfl⟩ := hb
    obtain ⟨nc, hnc, rfl⟩ := hc; obtain ⟨nd, hnd, rfl⟩ := hd
    obtain ⟨za, hza, rfl⟩ := Finset.mem_image.1 hna; obtain ⟨zb, hzb, rfl⟩ := Finset.mem_image.1 hnb
    obtain ⟨zc, hzc, rfl⟩ := Finset.mem_image.1 hnc; obtain ⟨zd, hzd, rfl⟩ := Finset.mem_image.1 hnd
    simp only [ZMod.natCast_zmod_val] at habcd ⊢
    exact hS za zb zc zd hza hzb hzc hzd habcd
  · intro n hn
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.1 hn
    have hx0 : x.val ≠ 0 := fun h => h0 ((ZMod.val_eq_zero x).1 h ▸ hxS)
    exact Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero hx0, Nat.le_pred_of_lt (ZMod.val_lt x)⟩

end Construction

/-
Every Sidon set S ⊆ [N] is contained in some maximal Sidon set M ⊆ [N].
-/
def MaximalSidonSubset (U : Finset ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ U ∧ Sidon (S : Set ℕ) ∧ ∀ S' : Finset ℕ, S' ⊆ U → Sidon (S' : Set ℕ) → S ⊆ S' → S = S'

lemma lem_extend (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N) (hSidon : Sidon (S : Set ℕ)) :
    ∃ M, MaximalSidonSubset (Finset.range N) M ∧ S ⊆ M := by
      -- By definition of maximal Sidon subset, there exists a maximal Sidon
      -- subset $M$ of $Finset.range N$ such that $S \subseteq M$.
      have h_max :
          ∃ M : Finset ℕ,
            S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N ∧
              ∀ M' : Finset ℕ,
                Sidon (M' : Set ℕ) →
                  M ⊆ M' → M' ⊆ Finset.range N → M = M' := by
        -- Apply the definition of maximalSidonSubset to obtain such an M.
        obtain ⟨M, hM⟩ :
            ∃ M ∈
                {M : Finset ℕ |
                  S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N},
              ∀ M' ∈
                {M : Finset ℕ |
                  S ⊆ M ∧ Sidon (M : Set ℕ) ∧ M ⊆ Finset.range N},
                M.card ≥ M'.card := by
          apply_rules [ Set.exists_max_image ];
          · exact
              Set.finite_iff_bddAbove.mpr
                ⟨Finset.range N, fun M hM => hM.2.2⟩;
          · exact ⟨ S, ⟨ Finset.Subset.refl _, hSidon, hS ⟩ ⟩;
        refine ⟨ M, hM.1.1, hM.1.2.1, hM.1.2.2, fun M' hM' hM'' hM''' => ?_ ⟩;
        exact
          Finset.eq_of_subset_of_card_le hM''
            (by
              linarith [
                hM.2 M' ⟨Finset.Subset.trans hM.1.1 hM'', hM', hM'''⟩
              ]);
      obtain ⟨ M, hM₁, hM₂, hM₃, hM₄ ⟩ := h_max; use M; unfold MaximalSidonSubset; aesop;

/-
Let A(N) denote the number of Sidon subsets of [N], and let A_1(N) denote the
number of maximal Sidon subsets of [N].
-/
attribute [local instance] Classical.propDecidable

noncomputable def A (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S : Finset ℕ => Sidon (S : Set ℕ))).card

noncomputable def A1 (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => MaximalSidonSubset (Finset.range N) S)).card

/-
For every N >= 1, A(N) <= A_1(N) * 2^(f(N)).
-/
lemma lem_cover (N : ℕ) : (A N : ℝ) ≤ (A1 N : ℝ) * (2 : ℝ) ^ (f N : ℝ) := by
  -- Every Sidon set is contained in at least one maximal Sidon set.
  have h_contained :
      ∀ S ∈
          Finset.filter (fun S : Finset ℕ => Sidon (S : Set ℕ))
            (Finset.powerset (Finset.range N)),
        ∃ M ∈
          Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S)
            (Finset.powerset (Finset.range N)),
          S ⊆ M := by
    intro S hS;
    -- By Lemma~\ref{lem:extend}, every Sidon set is contained in at least one
    -- maximal Sidon set. Let's obtain such a maximal Sidon set $M$.
    obtain ⟨M, hM⟩ : ∃ M : Finset ℕ, MaximalSidonSubset (Finset.range N) M ∧ S ⊆ M := by
      have hS_subset : S ⊆ Finset.range N :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
      have hS_sidon : Sidon (S : Set ℕ) := (Finset.mem_filter.mp hS).2
      exact
        lem_extend N S hS_subset hS_sidon |>
          fun ⟨ M, hM₁, hM₂ ⟩ => ⟨ M, hM₁, hM₂ ⟩
    exact ⟨ M, Finset.mem_filter.mpr ⟨ Finset.mem_powerset.mpr hM.1.1, hM.1 ⟩, hM.2 ⟩;
  -- Since $\abs{M}\le f(N)$, the family of all Sidon sets is contained in the union
  -- of the families of subsets of maximal Sidon sets, hence
  have h_union :
      Finset.filter (fun S : Finset ℕ => Sidon (S : Set ℕ)) (Finset.powerset (Finset.range N)) ⊆
        Finset.biUnion
          (Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S)
            (Finset.powerset (Finset.range N)))
          (fun M => Finset.powerset M) := by
    intro S hS; specialize h_contained S hS; aesop;
  -- Since $\abs{M}\le f(N)$, each maximal Sidon set $M$ contains at most $2^{f(N)}$ Sidon subsets.
  have h_max_subset :
      ∀ M ∈
          Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S)
            (Finset.powerset (Finset.range N)),
        (Finset.powerset M).card ≤ 2 ^ (f N : ℕ) := by
    -- Since $\abs{M}\le f(N)$, each maximal Sidon set $M$ contains at most $2^{f(N)}$ subsets.
    intros M hM
    have h_card_M : M.card ≤ f N := by
      refine le_trans ?_ ( Finset.le_sup <| show M.image ( fun x => x + 1 ) ∈ _ from ?_ );
      · rw [ Finset.card_image_of_injective _ Nat.succ_injective ];
      · simp_all +decide [ Finset.subset_iff, MaximalSidonSubset ];
        intro a b c d ha hb hc hd habcd
        obtain ⟨ x, hx, rfl ⟩ := ha
        obtain ⟨ y, hy, rfl ⟩ := hb
        obtain ⟨ z, hz, rfl ⟩ := hc
        obtain ⟨ w, hw, rfl ⟩ := hd
        simp_all +decide [Sidon];
        convert
          congr_arg (fun s : Set ℕ => s.image (fun n => n + 1))
            (hM.2.1 x y z w hx hy hz hw (by linarith))
          using 1 <;> ext <;> simp +decide
        · tauto;
        · tauto
    simp
    exact pow_le_pow_right₀ ( by decide ) h_card_M;
  have h_card_union :
      (Finset.filter (fun S : Finset ℕ => Sidon (S : Set ℕ))
        (Finset.powerset (Finset.range N))).card ≤
        (Finset.filter (fun S => MaximalSidonSubset (Finset.range N) S)
          (Finset.powerset (Finset.range N))).card * 2 ^ (f N : ℕ) := by
    refine le_trans ( Finset.card_le_card h_union ) ?_;
    refine le_trans ( Finset.card_biUnion_le ) ?_;
    refine le_trans ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ 2 ^ f N from ?_ ) ?_;
    · exact h_max_subset x hx
    · norm_num [ Finset.sum_const ];
  exact_mod_cast (by simpa [A, A1] using h_card_union)

/-
For every N >= 1, A_1(N) >= A(N) * 2^(-f(N)).
-/
lemma cor_ratio (N : ℕ) : (A1 N : ℝ) ≥ (A N : ℝ) * (2 : ℝ) ^ (-(f N : ℝ)) := by
  have := @lem_cover N;
  norm_num [ Real.rpow_neg ] at *;
  rwa [ ← div_eq_mul_inv, div_le_iff₀ ( by positivity ) ]

/-
Let p be prime, and let g be a generator of the multiplicative group F_p^x.
In the abelian group G := Z_{p-1} x Z_p, define S := {(i, g^i) : i in Z_{p-1}}.
Then S is Sidon in G.
-/
def ruzsa_set (p : ℕ) (g : ZMod p) : Finset (ZMod (p - 1) × ZMod p) :=
  (Finset.range (p - 1)).image (fun (i : ℕ) => ((i : ZMod (p - 1)), g ^ i))

lemma lem_ruzsa_group (p : ℕ) (hp : p.Prime) (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) :
    Sidon (ruzsa_set p g : Set (ZMod (p - 1) × ZMod p)) := by
      intro a b c d;
      simp [ruzsa_set];
      rintro x hx rfl y hy rfl z hz rfl w hw rfl h; have := Fact.mk hp; simp_all +decide
      -- Since $g$ is a generator of the multiplicative group modulo $p$, we have
      -- $g^{i_1}g^{i_2} \equiv g^{i_3}g^{i_4} \pmod{p}$.
      have h_prod : g ^ x * g ^ y = g ^ z * g ^ w := by
        have h_exp : (x + y : ℕ) ≡ (z + w : ℕ) [MOD (p - 1)] := by
          have := Fact.mk hp; rw [ ← ZMod.natCast_eq_natCast_iff ] ; aesop;
        rw [
          ← pow_add, ← pow_add,
          ← Nat.mod_add_div (x + y) (p - 1),
          ← Nat.mod_add_div (z + w) (p - 1), h_exp
        ];
        simp +decide [ pow_add, pow_mul, hg.pow_eq_one ];
      -- Since $g$ is a generator of the multiplicative group modulo $p$, this
      -- congruence implies either $g^{i_1} = g^{i_3}$ and $g^{i_2} = g^{i_4}$,
      -- or $g^{i_1} = g^{i_4}$ and $g^{i_2} = g^{i_3}$.
      have h_cases : g ^ x = g ^ z ∧ g ^ y = g ^ w ∨ g ^ x = g ^ w ∧ g ^ y = g ^ z := by
        have h_cases : (g ^ x - g ^ z) * (g ^ y - g ^ z) = 0 := by
          grind +ring;
        have := Fact.mk hp; simp_all +decide [ sub_eq_iff_eq_add ] ;
        grind;
      cases h_cases <;> simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      · have := hg.pow_inj (by linarith : x < p - 1) (by linarith : z < p - 1)
        have := hg.pow_inj (by linarith : y < p - 1) (by linarith : w < p - 1)
        aesop;
      · have := hg.pow_inj (by linarith : x < p - 1) (by linarith : w < p - 1)
        have := hg.pow_inj (by linarith : y < p - 1) (by linarith : z < p - 1)
        simp_all +decide [ add_comm ] ;

/-
Let p be prime and set m := p(p-1). There exists a set T in Z_m with |T| =
p-1 such that T is a Sidon set modulo m.
-/
lemma lem_modular (p : ℕ) (hp : p.Prime) :
    ∃ T : Finset (ZMod (p * (p - 1))), T.card = p - 1 ∧ Sidon (T : Set (ZMod (p * (p - 1)))) := by
      -- Let $g$ be a generator of the multiplicative group of integers modulo $p$.
      obtain ⟨g, hg⟩ : ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) := by
        have := Fact.mk hp;
        exact HasEnoughRootsOfUnity.prim;
      -- By Lemma 4.1, the set $S = \{(i, g^i) : i \in \mathbb{Z}_{p-1}\}$
      -- is Sidon in the group $G = \mathbb{Z}_{p-1} \times \mathbb{Z}_p$.
      have h_Sidon_S : Sidon (ruzsa_set p g : Set (ZMod (p - 1) × ZMod p)) := by
        convert lem_ruzsa_group p hp g hg;
      -- Since $\gcd(p, p-1) = 1$, the Chinese Remainder Theorem gives a group
      -- isomorphism $\mathbb{Z}_{p-1} \times \mathbb{Z}_p \cong \mathbb{Z}_m$.
      have h_iso : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod (p * (p - 1))) := by
        have h_iso : Nonempty (ZMod (p - 1) × ZMod p ≃+ ZMod ((p - 1) * p)) := by
          have h_coprime : Nat.gcd (p - 1) p = 1 := by
            simp +decide [ hp.one_lt.le ]
          refine ⟨ ?_ ⟩;
          exact ( ZMod.chineseRemainder h_coprime ).toAddEquiv.symm
        generalize_proofs at *;
        rwa [ Nat.mul_comm ] at h_iso;
      obtain ⟨ f ⟩ := h_iso;
      refine ⟨
        Finset.image (fun x : ZMod (p - 1) × ZMod p => f x) (ruzsa_set p g),
        ?_, ?_
      ⟩ <;> simp_all +decide [ Sidon ];
      · rw [ Finset.card_image_of_injective _ f.injective, Finset.card_eq_of_bijective ];
        · use fun i hi => ( i, g ^ i );
        · unfold ruzsa_set; aesop;
        · exact fun i hi => Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr hi, rfl ⟩;
        · simp +contextual [ ZMod.natCast_eq_natCast_iff' ];
          exact fun i j hi hj hij h => Nat.mod_eq_of_lt hi ▸ Nat.mod_eq_of_lt hj ▸ hij ▸ rfl;
      · intro a b c d x y hx hy z t hz ht u v hu hv w x' hw hx' habcd
        have := f.injective
        simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
        specialize h_Sidon_S x y z t u v w x' hx hz hu hw
        simp_all +decide [ ← hy, ← ht, ← hv, ← hx', ← map_add ] ;

/-
S_chi is a subset of [4m].
-/
def S_chi (m : ℕ) (T : Finset ℕ) (chi : {x // x ∈ T} → Fin 5) : Finset ℕ :=
  (T.attach.filter (fun t => chi t ≠ 0)).image (fun t => t.val + ((chi t).val - 1) * m)

lemma S_chi_subset (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (chi : {x // x ∈ T} → Fin 5) :
    S_chi m T chi ⊆ Finset.range (4 * m) := by
      rintro x hx;
      obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx;
      have := Finset.mem_range.mp (hT y.2)
      rcases x : (chi y : Fin 5) with (_ | _ | _ | _ | _ | k) <;>
        simp_all +decide
      · linarith
      · grind;
      · linarith;
      · grind;
      · linarith

/-
S_chi is a Sidon set.
-/
lemma S_chi_is_Sidon (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (hSidon : SidonMod m (T : Set ℕ)) (chi : {x // x ∈ T} → Fin 5) :
    Sidon (S_chi m T chi : Set ℕ) := by
      intro a ha b hb c hc d hd habcd;
      -- By definition of $S_\chi$, there exist $t_a, t_b, t_c, t_d \in T$ such
      -- that $a = t_a + (\chi(t_a)-1)m$, $b = t_b + (\chi(t_b)-1)m$,
      -- $c = t_c + (\chi(t_c)-1)m$, and $d = t_d + (\chi(t_d)-1)m$.
      obtain ⟨ta, hta, ha_eq⟩ : ∃ ta : T, a = ta.val + ((chi ta).val - 1) * m := by
        unfold S_chi at c; aesop;
      obtain ⟨tb, htb, hb_eq⟩ : ∃ tb : T, ha = tb.val + ((chi tb).val - 1) * m := by
        unfold S_chi at hc; aesop;
      obtain ⟨tc, htc, hc_eq⟩ : ∃ tc : T, b = tc.val + ((chi tc).val - 1) * m := by
        unfold S_chi at d; aesop;
      obtain ⟨td, htd, hd_eq⟩ : ∃ td : T, hb = td.val + ((chi td).val - 1) * m := by
        unfold S_chi at hd; aesop;
      -- Since $T$ is Sidon modulo $m$, we have $\{t_a, t_b\} = \{t_c, t_d\}$ as multisets in $Z_m$.
      have h_multiset_eq : ({(ta : ℕ), (tb : ℕ)} : Set ℕ) = ({(tc : ℕ), (td : ℕ)} : Set ℕ) := by
        have h_multiset_eq :
            ({(ta : ZMod m), (tb : ZMod m)} : Set (ZMod m)) =
              ({(tc : ZMod m), (td : ZMod m)} : Set (ZMod m)) := by
          replace habcd := congr_arg ( ( ↑ ) : ℕ → ZMod m ) habcd ; aesop;
        convert set_pair_eq_of_zmod_pair_eq m _ _ _ _ h_multiset_eq using 1;
        · exact ⟨ by linarith ⟩;
        · exact Finset.mem_range.mp ( hT ta.2 );
        · exact Finset.mem_range.mp ( hT tb.2 );
        · exact Finset.mem_range.mp ( hT tc.2 );
        · exact Finset.mem_range.mp ( hT td.2 );
      grind

/-
The map chi -> S_chi is injective.
-/
lemma S_chi_injective (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m) :
    Function.Injective (S_chi m T) := by
      -- If $S_{\chi_1} = S_{\chi_2}$, then for every $t \in T$, $\chi_1(t) = \chi_2(t)$.
      intros chi1 chi2 h_eq
      have h_eq_values : ∀ t : T, chi1 t ≠ 0 → chi2 t ≠ 0 → chi1 t = chi2 t := by
        intro t ht1 ht2
        have h_eq_t : t.val + ((chi1 t).val - 1) * m ∈ S_chi m T chi2 := by
          exact
            h_eq ▸
              Finset.mem_image.mpr
                ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ht1⟩, rfl⟩;
        -- Since $t$ is in $T$, we know that $t.val < m$.
        have h_t_val_lt_m : t.val < m := by
          exact Finset.mem_range.mp ( hT t.2 );
        -- Since $t$ is in $T$, we know that $t.val < m$, so we can compare the
        -- representatives modulo $m$.
        obtain ⟨t', ht', ht'_eq⟩ :
            ∃ t' : T,
              t'.val = t.val ∧ ((chi1 t).val - 1) = ((chi2 t').val - 1) := by
          obtain ⟨ t', ht', ht'_eq ⟩ := Finset.mem_image.mp h_eq_t;
          have := congr_arg (· % m) ht'_eq
          norm_num [
            Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt h_t_val_lt_m,
            Nat.mod_eq_of_lt
              (show (t' : ℕ) < m from Finset.mem_range.mp (hT t'.2))
          ] at this
          aesop;
        grind;
      ext t
      specialize h_eq_values t
      by_cases h1 : chi1 t = 0 <;>
        by_cases h2 : chi2 t = 0 <;>
        simp_all +decide [Finset.ext_iff];
      · contrapose! h_eq; simp_all +decide [ S_chi ] ;
        refine ⟨ t.val + ((chi2 t).val - 1) * m, Or.inr ⟨ ?_, t, t.2, h2, rfl ⟩ ⟩;
        intro x hx hx' H
        have := congr_arg (· % m) H
        norm_num [
          Nat.add_mod, Nat.mul_mod,
          Nat.mod_eq_of_lt (show x < m from Finset.mem_range.mp (hT hx)),
          Nat.mod_eq_of_lt (show (t : ℕ) < m from Finset.mem_range.mp (hT t.2))
        ] at this;
        cases t ; aesop;
      · contrapose! h_eq;
        refine ⟨ t.val + ((chi1 t).val - 1) * m,
          Or.inl
            ⟨Finset.mem_image.mpr
              ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, h1⟩, rfl⟩, ?_⟩⟩
        simp_all +decide [ S_chi ];
        intro x hx hx' H
        have := congr_arg (· % m) H
        norm_num [
          Nat.add_mod, Nat.mul_mod,
          Nat.mod_eq_of_lt (show t.val < m from Finset.mem_range.mp (hT t.2)),
          Nat.mod_eq_of_lt (show x < m from Finset.mem_range.mp (hT hx))
        ] at this;
        cases t ; aesop

/-
A(4m) >= 5^|T|.
-/
lemma lem_four_block (m : ℕ) (hm : m ≥ 1) (T : Finset ℕ) (hT : T ⊆ Finset.range m)
    (hSidon : SidonMod m (T : Set ℕ)) :
    A (4 * m) ≥ 5 ^ T.card := by
      have hA_ge :
          Set.ncard
            (Set.image (fun f : { x // x ∈ T } → Fin 5 => S_chi m T f)
              (Set.univ : Set (_ → Fin 5))) ≥
            5 ^ T.card := by
        rw [
          Set.ncard_image_of_injective _ (S_chi_injective m hm T hT),
          Set.ncard_univ
        ]
        norm_num [ Set.ncard_eq_toFinset_card' ] ;
      refine le_trans hA_ge ?_;
      have h_image_subset :
          Set.image (fun f : { x // x ∈ T } → Fin 5 => S_chi m T f)
            (Set.univ : Set (_ → Fin 5)) ⊆
            {S : Finset ℕ | S ⊆ Finset.range (4 * m) ∧ Sidon (S : Set ℕ)} := by
        intro S hSaesop;
        obtain ⟨ f, _, rfl ⟩ := hSaesop
        exact ⟨ S_chi_subset m hm T hT f, S_chi_is_Sidon m hm T hT hSidon f ⟩ ;
      have h_card_image :
          Set.ncard
            {S : Finset ℕ | S ⊆ Finset.range (4 * m) ∧ Sidon (S : Set ℕ)} ≤
            (Finset.powerset (Finset.range (4 * m)) |>.filter
              (fun S : Finset ℕ => Sidon (S : Set ℕ))).card := by
        rw [show
            {S : Finset ℕ | S ⊆ Finset.range (4 * m) ∧ Sidon (S : Set ℕ)} =
              (↑(Finset.filter (fun S : Finset ℕ => Sidon (S : Set ℕ))
                (Finset.powerset (Finset.range (4 * m)))) : Set (Finset ℕ)) by
          ext S
          simp [Finset.mem_powerset]]
        exact le_of_eq (Set.ncard_coe_finset _)
      refine le_trans ?_ (by simpa [A] using h_card_image);
      apply_rules [ Set.ncard_le_ncard ];
      exact
        Set.finite_iff_bddAbove.mpr
          ⟨Finset.range (4 * m), fun S hS => Finset.subset_iff.mpr hS.1⟩

/-
Let p be prime. Then A(4p(p-1)) >= 5^(p-1).
-/
lemma prop_lower_special_ineq (p : ℕ) (hp : p.Prime) :
    A (4 * p * (p - 1)) ≥ 5 ^ (p - 1) := by
      have := lem_modular p hp;
      -- Let $T$ be a Sidon set modulo $m = p(p-1)$ with $|T| = p-1$.
      obtain ⟨T, hT_card, hT_sidon⟩ := this;
      -- Let $T$ be a Sidon set modulo $m = p(p-1)$ with $|T| = p-1$. We can
      -- lift $T$ to a Sidon set $T'$ in $\mathbb{N}$.
      obtain ⟨T', hT'_card, hT'_sidon⟩ :
          ∃ T' : Finset ℕ,
            T'.card = p - 1 ∧ SidonMod (p * (p - 1)) (T' : Set ℕ) ∧
              (T' : Set ℕ) ⊆ Finset.Icc 1 (p * (p - 1) - 1) := by
        -- Apply the shift_sidon_mod lemma to obtain a Sidon set $T'$ in
        -- $\mathbb{N}$ with the desired properties.
        obtain ⟨T', hT'_card, hT'_sidon, hT'_subset⟩ :
            ∃ T' : Finset (ZMod (p * (p - 1))),
              T'.card = p - 1 ∧ Sidon (T' : Set (ZMod (p * (p - 1)))) ∧
                (0 : ZMod (p * (p - 1))) ∉ T' := by
          have :=
            shift_sidon_mod (p * (p - 1))
              (by nlinarith [hp.two_le, Nat.sub_pos_of_lt hp.one_lt])
              T hT_sidon
              (by nlinarith [hp.two_le, Nat.sub_pos_of_lt hp.one_lt]);
          grind +ring;
        have := @lift_sidon_mod ( p * ( p - 1 ) ) ?_ T' hT'_sidon hT'_subset;
        · aesop;
        · rcases p with ( _ | _ | p ) <;> simp_all +decide;
          nlinarith only [ hp.two_le ];
      have := @lem_four_block ( p * ( p - 1 ) ) ?_ T' ?_ ?_ <;> simp_all +decide [ mul_assoc ];
      · exact Nat.mul_pos hp.pos ( Nat.sub_pos_of_lt hp.one_lt );
      · exact fun x hx =>
          Finset.mem_range.mpr
            (lt_of_le_of_lt (hT'_sidon.2 hx |>.2)
              (Nat.pred_lt
                (ne_bot_of_gt (Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hp.one_lt)))))

/-
For every fixed epsilon in (0,1) and all sufficiently large x, the interval
((1-epsilon)x, x] contains a prime.
-/
lemma lem_prime_near (ε : ℝ) (hε : ε ∈ Set.Ioo 0 1) :
    ∀ᶠ x : ℝ in Filter.atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p ≤ x := by
      -- By the Prime Number Theorem, there exists a prime $p$ in the interval
      -- $(x, (1 + \epsilon)x)$ for sufficiently large $x$.
      have h_prime_between : ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < (1 + ε) * x := by
        convert prime_between hε.1 using 1;
      -- Let $y = (1 - \epsilon)x$. Then
      -- $(1 + \delta)y = (1 + \frac{\epsilon}{1-\epsilon})(1-\epsilon)x = x$.
      have := h_prime_between;
      norm_num at *;
      obtain ⟨ a, ha ⟩ := this
      use (a : ℝ) / (1 - ε)
      intro b hb
      obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ :=
        ha ((1 - ε) * b)
          (by
            nlinarith [
              mul_div_cancel₀ (a : ℝ) (by linarith : (1 - ε) ≠ 0)
            ])
      exact ⟨ p, hp₁, by nlinarith, by nlinarith ⟩ ;

/-
A(N) is monotonically increasing.
-/
lemma A_mono {N M : ℕ} (h : N ≤ M) : A N ≤ A M := by
  -- By definition of $A$, we know that every Sidon subset of $[N]$ is also a subset of $[M]$.
  have h_subset : ∀ S : Finset ℕ, S ⊆ Finset.range N → Sidon (S : Set ℕ) → S ⊆ Finset.range M := by
    exact fun S hS hSidon => Finset.Subset.trans hS ( Finset.range_mono h );
  refine Finset.card_le_card ?_;
  intro S hS; aesop;

/-
For any c < 1/2 log 5, eventually log A(N) / sqrt N >= c.
-/
lemma eventually_lower_bound (c : ℝ) (hc : c < Real.log 5 / 2) :
    ∀ᶠ N : ℕ in Filter.atTop, Real.log (A N : ℝ) / Real.sqrt N ≥ c := by
      -- Since $c < \frac{1}{2}\log 5$, we can choose $\varepsilon > 0$ such
      -- that $c < (1-\varepsilon)\frac{1}{2}\log 5$.
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, c < (1 - ε) * (Real.log 5 / 2) := by
        exact ⟨
          (1 - c / (Real.log 5 / 2)) / 2,
          by
            nlinarith [
              Real.log_pos (show (5 : ℝ) > 1 by norm_num),
              mul_div_cancel₀ c
                (ne_of_gt (by positivity : 0 < Real.log 5 / 2))
            ],
          by
            nlinarith [
              Real.log_pos (show (5 : ℝ) > 1 by norm_num),
              mul_div_cancel₀ c
                (ne_of_gt (by positivity : 0 < Real.log 5 / 2))
            ]
        ⟩;
      -- For large $N$, let $x = \frac{1}{2}\sqrt{N}$. By `lem_prime_near`,
      -- there exists a prime $p \in ((1-\varepsilon)x, x]$.
      have h_prime :
          ∀ᶠ N : ℕ in Filter.atTop,
            ∃ p : ℕ,
              p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧
                p ≤ (1 / 2) * Real.sqrt N := by
        have h_prime :
            ∀ᶠ x : ℝ in Filter.atTop,
              ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p ≤ x := by
          by_cases hε_lt_1 : ε < 1;
          · convert lem_prime_near ε ⟨ hε_pos, hε_lt_1 ⟩ using 1;
          · exact
              Filter.eventually_atTop.mpr
                ⟨2, fun x hx =>
                  ⟨2, by norm_num,
                    by norm_num; nlinarith [Real.log_pos (show 5 > 1 by norm_num)],
                    by norm_num; linarith⟩⟩;
        rw [ Filter.eventually_atTop ] at *;
        obtain ⟨ a, ha ⟩ := h_prime
        use Nat.ceil (a ^ 2 * 4)
        intro b hb
        obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ :=
          ha (Real.sqrt b / 2)
            (by
              nlinarith [
                Nat.ceil_le.mp hb, Real.sqrt_nonneg b,
                Real.sq_sqrt (Nat.cast_nonneg b)
              ])
        exact ⟨
          p, hp₁,
          by nlinarith [Real.sqrt_nonneg b, Real.sq_sqrt (Nat.cast_nonneg b)],
          by nlinarith [Real.sqrt_nonneg b, Real.sq_sqrt (Nat.cast_nonneg b)]
        ⟩ ;
      -- Let $N_p = 4p(p-1)$. Then $N_p \le 4x ^ 2 = N$.
      have h_Np :
          ∀ᶠ N : ℕ in Filter.atTop,
            ∃ p : ℕ,
              p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧
                p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N := by
        filter_upwards [h_prime, Filter.eventually_gt_atTop 0] with N hN hN'
        rcases hN with ⟨ p, hp₁, hp₂, hp₃ ⟩
        refine ⟨ p, hp₁, hp₂, hp₃, ?_ ⟩
        rcases p with (_ | _ | p) <;> norm_num at *
        exact_mod_cast
          (by
            nlinarith [Real.mul_self_sqrt (Nat.cast_nonneg N)] :
            (4 : ℝ) * (p + 1 + 1) * (p + 1) ≤ N);
      -- By monotonicity (`A_mono`), $A(N) \ge A(N_p)$.
      have h_monotone :
          ∀ᶠ N : ℕ in Filter.atTop,
            ∃ p : ℕ,
              p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧
                p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N ∧
                  (A N : ℝ) ≥ 5 ^ (p - 1) := by
        filter_upwards [ h_Np ] with N hN;
        obtain ⟨ p, hp₁, hp₂, hp₃, hp₄ ⟩ := hN
        exact ⟨ p, hp₁, hp₂, hp₃, hp₄, by
          exact_mod_cast
            le_trans (prop_lower_special_ineq p hp₁) (A_mono (by linarith)) ⟩ ;
      -- So $\frac{\log A(N)}{\sqrt{N}}$ is bounded below by the explicit
      -- expression coming from the prime $p$.
      have h_bound :
          ∀ᶠ N : ℕ in Filter.atTop,
            ∃ p : ℕ,
              p.Prime ∧ (1 - ε) * (1 / 2) * Real.sqrt N < p ∧
                p ≤ (1 / 2) * Real.sqrt N ∧ 4 * p * (p - 1) ≤ N ∧
                  Real.log (A N) / Real.sqrt N ≥
                    ((1 - ε) / 2) * Real.log 5 - Real.log 5 / Real.sqrt N := by
        field_simp;
        filter_upwards [h_monotone, Filter.eventually_gt_atTop 0] with N hN hN'
        rcases hN with ⟨ p, hp₁, hp₂, hp₃, hp₄, hp₅ ⟩
        refine ⟨ p, hp₁, ?_, ?_, hp₄, ?_ ⟩ <;> try linarith;
        -- Using the fact that $A(N) \geq 5^{p-1}$, we have $\log A(N) \geq (p-1) \log 5$.
        have h_log_bound : Real.log (A N) ≥ (p - 1) * Real.log 5 := by
          rcases p with ( _ | _ | p ) <;> norm_num at *;
          simpa using Real.log_le_log ( by positivity ) hp₅;
        rw [le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN'))]
        nlinarith [
          Real.sqrt_nonneg N,
          Real.sq_sqrt (Nat.cast_nonneg N),
          Real.log_pos (show (5 : ℝ) > 1 by norm_num),
          mul_div_cancel₀ (2 : ℝ)
            (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN')))
        ] ;
      -- As $N \to \infty$, the term $\frac{\log 5}{\sqrt{N}}$ tends to $0$.
      have h_log_div_sqrt :
          Filter.Tendsto (fun N : ℕ => Real.log 5 / Real.sqrt N)
            Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          tendsto_const_nhds.mul (tendsto_inv_atTop_nhds_zero_nat.sqrt);
      filter_upwards [
        h_bound,
        h_log_div_sqrt.eventually
          (gt_mem_nhds <|
            show 0 < (1 - ε) * (Real.log 5 / 2) - c by
              linarith)
      ] with N hN₁ hN₂ using by
        obtain ⟨ p, hp₁, hp₂, hp₃, hp₄, hp₅ ⟩ := hN₁
        linarith;

/-
Assume the prime number theorem, and assume the standard extremal bound
f(N)=(1+o(1))sqrt(N). Then log A_1(N) >= (eta + o(1))sqrt(N).
-/
noncomputable def eta : ℝ := 1 / 2 * Real.log (5 / 4)

theorem thm_main
    (h_f :
      Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ∀ c < eta, ∀ᶠ N : ℕ in Filter.atTop, Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
      field_simp;
      -- By definition of eta, we have eta = log(5 / 4) / 2.
      have h_eta : eta = Real.log (5 / 4) / 2 := by
        unfold eta; norm_num; ring;
      -- By definition of $A1$, we know that $A1(N) \geq A(N) \cdot 2^{-f(N)}$.
      have h_A1_lower_bound : ∀ N, A1 N ≥ A N * (2 : ℝ) ^ (-(f N) : ℝ) := by
        exact fun N => cor_ratio N;
      -- Taking logarithms on both sides gives
      -- $\log A1(N) \geq \log A(N) - f(N) \log 2$.
      have h_log_A1_lower_bound :
          ∀ N, Real.log (A1 N : ℝ) ≥
            Real.log (A N : ℝ) - (f N : ℝ) * Real.log 2 := by
        intro N
        specialize h_A1_lower_bound N
        by_cases h : A N = 0 <;> simp_all +decide [ Real.rpow_def_of_pos ] ;
        · -- If $A N = 0$, the empty set gives a contradiction.
          have h_contra : A N ≠ 0 := by
            refine ne_of_gt ( Finset.card_pos.mpr ?_ );
            refine ⟨ ∅, ?_ ⟩ ; simp +decide [ Sidon ];
          contradiction;
        · have := Real.log_le_log (by positivity) h_A1_lower_bound
          norm_num [Real.log_mul, Real.exp_ne_zero, h] at this ⊢
          linarith;
      -- By definition of $A$, we know that $\log A(N) \geq (\frac{1}{2} \log 5 + o(1)) \sqrt{N}$.
      have h_log_A_lower_bound :
          ∀ c < Real.log 5 / 2,
            ∀ᶠ N in Filter.atTop,
              Real.log (A N : ℝ) ≥ (c : ℝ) * Real.sqrt N := by
        intro c hc
        have h_log_A_lower_bound :
            ∀ᶠ N in Filter.atTop, Real.log (A N : ℝ) / Real.sqrt N ≥ c := by
          exact eventually_lower_bound c hc;
        filter_upwards [h_log_A_lower_bound, Filter.eventually_gt_atTop 0]
          with N hN hN' using by
          rw [ge_iff_le] at *
          rw [le_div_iff₀ (Real.sqrt_pos.mpr <| Nat.cast_pos.mpr hN')] at *
          linarith;
      -- By definition of $f$, we know that $f(N) = (1 + o(1)) \sqrt{N}$.
      have h_f_lower_bound :
          ∀ ε > 0,
            ∀ᶠ N in Filter.atTop, (f N : ℝ) ≤ (1 + ε) * Real.sqrt N := by
        intro ε hε_pos
        have h_f_lower_bound :
            ∀ᶠ N in Filter.atTop, (f N : ℝ) / Real.sqrt N ≤ 1 + ε := by
          exact h_f.eventually ( ge_mem_nhds <| by linarith );
        filter_upwards [h_f_lower_bound, Filter.eventually_gt_atTop 0]
          with N hN hN' using by
          rwa [div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN'))] at hN;
      -- Combine the inequalities from h_log_A_lower_bound and h_f_lower_bound.
      intros c hc
      obtain ⟨ε, hε_pos, hε⟩ :
          ∃ ε > 0, (Real.log 5 / 2 - ε) - (1 + ε) * Real.log 2 > c := by
        have h_eps :
            Filter.Tendsto
              (fun ε : ℝ => (Real.log 5 / 2 - ε) - (1 + ε) * Real.log 2)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log 5 / 2 - Real.log 2)) := by
          exact
            tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto' (by continuity) _ _ (by norm_num));
        have :=
          h_eps.eventually
            (lt_mem_nhds <|
              show log 5 / 2 - log 2 > c by
                rw [h_eta] at hc
                rw [
                  show (5 / 4 : ℝ) = 5 / 2 ^ 2 by norm_num,
                  Real.log_div, Real.log_pow
                ] at hc <;> norm_num at *
                linarith)
        have := this.and self_mem_nhdsWithin
        obtain ⟨ ε, hε₁, hε₂ ⟩ := this.exists
        exact ⟨ ε, hε₂, hε₁ ⟩ ;
      filter_upwards [
        h_log_A_lower_bound (Real.log 5 / 2 - ε) (by linarith),
        h_f_lower_bound ε hε_pos,
        Filter.eventually_gt_atTop 0
      ] with N hN₁ hN₂ hN₃ using by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN₃))]
        nlinarith [
          h_log_A1_lower_bound N, Real.sqrt_nonneg N,
          Real.sq_sqrt (Nat.cast_nonneg N), Real.log_nonneg one_le_two
        ] ;

/-
A_1(N) is not of the form 2^(o(sqrt(N))).
-/
theorem cor_answers_1
    (h_f :
      Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ¬ (fun N => Real.log (A1 N)) =o[Filter.atTop] (fun N => Real.sqrt N) := by
      -- By definition of `o`, it suffices to show that this limit is nonzero.
      suffices h_lim :
          Filter.Tendsto (fun N => Real.log (A1 N : ℝ) / Real.sqrt N)
            Filter.atTop (nhds (0)) → False by
        contrapose! h_lim; rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> aesop;
      -- By `thm_main`, eventually $\frac{\log A_1(N)}{\sqrt{N}} \geq c$.
      have h_log_lower_bound :
          ∀ c < eta,
            ∀ᶠ N : ℕ in Filter.atTop,
              Real.log (A1 N : ℝ) / Real.sqrt N ≥ c := by
        convert thm_main h_f using 1;
      intro H
      specialize h_log_lower_bound (eta / 2)
        (by
          linarith [
            show 0 < eta by
              exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
          ])
      replace h_log_lower_bound :=
        h_log_lower_bound.and
          (H.eventually
            (gt_mem_nhds
              (show 0 < eta / 2 by
                exact
                  div_pos
                    (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
                    zero_lt_two)))
      obtain ⟨ N, hN₁, hN₂ ⟩ := h_log_lower_bound.exists
      linarith;

/-
For every fixed c in (0, 1/2), A_1(N) >= 2^(N^c) for all sufficiently large N.
-/
theorem cor_answers_2
    (h_f :
      Filter.Tendsto (fun N => (f N : ℝ) / Real.sqrt N) Filter.atTop (nhds 1)) :
    ∀ c ∈ Set.Ioo 0 (1 / 2 : ℝ),
      ∀ᶠ N : ℕ in Filter.atTop, (A1 N : ℝ) ≥ 2 ^ ((N : ℝ) ^ c) := by
      field_simp;
      intro c hc
      have h_eventually :
          ∀ᶠ N : ℕ in Filter.atTop,
            Real.log (A1 N) ≥ (eta / 2) * Real.sqrt N := by
        have :=
          thm_main h_f (eta / 2)
            (by
              linarith [
                show eta > 0 by
                  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
              ]);
        filter_upwards [this, Filter.eventually_gt_atTop 0] with N hN hN' using by
          rw [ge_iff_le] at *
          rw [le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN'))] at *
          linarith;
      -- Since $N^c = o(\sqrt{N})$, eventually $(\eta/2)\sqrt{N} \ge N^c$.
      have h_eventually_ge :
          ∀ᶠ N : ℕ in Filter.atTop,
            (eta / 2) * Real.sqrt N ≥ (N : ℝ) ^ c * Real.log 2 := by
        field_simp;
        -- Divide by $\sqrt{N}$ to get $N^{c - 1/2} * \log 2 * 2 \leq \eta$.
        suffices h_div :
            ∀ᶠ N : ℕ in Filter.atTop,
              (N : ℝ) ^ (c - 1 / 2) * Real.log 2 * 2 ≤ eta by
          filter_upwards [h_div, Filter.eventually_gt_atTop 0] with N hN hN'
          rw [Real.sqrt_eq_rpow]
          rw [show (N : ℝ) ^ c =
              (N : ℝ) ^ (c - 1 / 2) * (N : ℝ) ^ (1 / 2 : ℝ) by
            rw [← Real.rpow_add (by positivity)]
            ring_nf]
          nlinarith [
            mul_le_mul_of_nonneg_right hN
              (show 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 2 by positivity)]
        field_simp;
        exact
          Filter.Tendsto.eventually
            (by
              simpa using
                Filter.Tendsto.mul
                  (Filter.Tendsto.mul tendsto_const_nhds <|
                    Filter.Tendsto.comp
                      (tendsto_rpow_neg_atTop
                        (show 0 < -((c * 2 - 1) / 2) by
                          linarith [hc.1, hc.2]))
                      tendsto_natCast_atTop_atTop)
                  tendsto_const_nhds)
            (ge_mem_nhds <|
              show 0 < eta from
                mul_pos (by norm_num) <| Real.log_pos <| by norm_num);
      filter_upwards [
        h_eventually, h_eventually_ge, Filter.eventually_gt_atTop 0
      ] with N hN₁ hN₂ hN₃;
      rw [
        ← Real.log_le_log_iff
          (by positivity)
          (Nat.cast_pos.mpr <|
            Nat.pos_of_ne_zero <| by
              intro h
              norm_num [h] at *
              nlinarith [
                Real.log_pos one_lt_two,
                show (N : ℝ) ^ c > 0 by positivity
              ]),
        Real.log_rpow
      ] <;> norm_num
      linarith [Real.log_pos one_lt_two]

/-
f(N) is monotonically increasing.
-/

/-
Lower bound for f(N): f(N) ≥ (1-ε)√N for large N.
-/

end

end Erdos862

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos43.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 43.
https://www.erdosproblems.com/forum/thread/43

Informal authors:
- Kevin Barreto

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos43.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/43.lean
-/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/

open scoped Pointwise

/-- The formal-conjectures definition of a Sidon set. -/
def IsSidon {α : Type*} [AddCommMonoid α] (A : Set α) : Prop :=
  ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

section
open Finset

instance (A : Finset α) [AddCommMonoid α] [DecidableEq α] :
    Decidable (IsSidon (A : Set α)) := by
  refine decidable_of_iff (∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
    i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)) ?_
  rfl

/-- The formal-conjectures maximum-cardinality definition. -/
private def _root_.Finset.maxSidonSubsetCard {α : Type*} [AddCommMonoid α]
    (A : Finset α) [DecidableEq α] : ℕ :=
  (A.powerset.filter fun B : Finset α ↦ IsSidon (B : Set α)).sup Finset.card

end

open Filter

noncomputable abbrev f (N : ℕ) : ℕ :=
  Finset.maxSidonSubsetCard (Finset.Icc 1 N)

private lemma isSidon_iff_erdos42 (A : Set ℕ) :
    IsSidon A ↔ Erdos42.IsSidon A := by
  constructor
  · intro h a₁ ha₁ a₂ ha₂ a₃ ha₃ a₄ ha₄ heq
    exact h a₁ ha₁ a₃ ha₃ a₂ ha₂ a₄ ha₄ heq
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    exact h hi₁ hi₂ hj₁ hj₂ heq

private lemma singleton_sidon (a : ℕ) : IsSidon ({a} : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
  simp_all

private lemma isSidon_iff_erdos862 {α : Type} [AddCommMonoid α] (A : Set α) :
    IsSidon A ↔ Erdos862.Sidon A := by
  constructor
  · intro h a b c d ha hb hc hd heq
    exact Set.pair_eq_pair_iff.mpr (h a ha c hc b hb d hd heq)
  · intro h i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
    exact Set.pair_eq_pair_iff.mp (h i₁ i₂ j₁ j₂ hi₁ hi₂ hj₁ hj₂ heq)

private lemma f_eq_erdos862_f (N : ℕ) : f N = Erdos862.f N := by
  classical
  unfold f Finset.maxSidonSubsetCard Erdos862.f
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact and_congr_right fun _ => isSidon_iff_erdos862 (A : Set ℕ)

private lemma sidon_of_sidonMod_of_lt {Q : ℕ} [NeZero Q] {T : Finset ℕ}
    (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) : IsSidon (T : Set ℕ) := by
  rw [isSidon_iff_erdos862]
  intro a b c d ha hb hc hd heq
  have hpair := hT (a : ZMod Q) (b : ZMod Q) (c : ZMod Q) (d : ZMod Q)
    ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      (by simpa using congrArg (fun n : ℕ => (n : ZMod Q)) heq)
  exact Erdos862.set_pair_eq_of_zmod_pair_eq Q (hlt a ha) (hlt b hb) (hlt c hc)
    (hlt d hd) hpair

private lemma orderedDiff_unique {Q : ℕ} [NeZero Q] {T : Finset ℕ}
    (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) {x y u v : ℕ}
    (hx : x ∈ T) (hy : y ∈ T) (hu : u ∈ T) (hv : v ∈ T)
    (hxy : x ≠ y)
    (hdiff : (x : ZMod Q) - y = (u : ZMod Q) - v) : x = u ∧ y = v := by
  have hsum : (x : ZMod Q) + v = u + y := by linear_combination hdiff
  have hpairs := hT (x : ZMod Q) (v : ZMod Q) (u : ZMod Q) (y : ZMod Q)
    ⟨x, hx, rfl⟩ ⟨v, hv, rfl⟩ ⟨u, hu, rfl⟩ ⟨y, hy, rfl⟩ hsum
  rcases Set.pair_eq_pair_iff.mp hpairs with h | h
  · exact ⟨Erdos862.eq_of_zmod_eq_of_lt Q x u (hlt x hx) (hlt u hu) h.1,
      Erdos862.eq_of_zmod_eq_of_lt Q y v (hlt y hy) (hlt v hv) h.2.symm⟩
  · exact False.elim (hxy <|
      Erdos862.eq_of_zmod_eq_of_lt Q x y (hlt x hx) (hlt y hy) h.1)

private lemma zmod_sub_val_even {Q x y : ℕ} [NeZero Q]
    (hx : x < Q) (hy : y < Q) (hQ : Even Q)
    (hpar : Even x ↔ Even y) : Even (((x : ZMod Q) - y).val) := by
  have hxval : (x : ZMod Q).val = x := ZMod.val_natCast_of_lt hx
  have hyval : (y : ZMod Q).val = y := ZMod.val_natCast_of_lt hy
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hyx : y ≤ x
  · rw [ZMod.val_sub (by simpa [hxval, hyval] using hyx), hxval, hyval]
    exact (Nat.even_sub hyx).2 hpar
  · have hxylt : x < y := lt_of_not_ge hyx
    have hsubne : (y : ZMod Q) - x ≠ 0 := by
      intro h
      have : (y : ZMod Q) = x := sub_eq_zero.mp h
      exact hxy (Erdos862.eq_of_zmod_eq_of_lt Q x y hx hy this.symm)
    rw [show (x : ZMod Q) - y = -((y : ZMod Q) - x) by abel]
    rw [ZMod.neg_val, if_neg hsubne]
    rw [ZMod.val_sub (by simpa [hxval, hyval] using hxylt.le), hxval, hyval]
    apply (Nat.even_sub (by omega : y - x ≤ Q)).2
    constructor
    · intro _
      exact (Nat.even_sub hxylt.le).2 hpar.symm
    · intro _
      exact hQ

private lemma parity_count {Q N : ℕ} [NeZero Q] {T : Finset ℕ}
    (hQeq : Q = 2 * N) (hT : Erdos862.SidonMod Q (T : Set ℕ))
    (hlt : ∀ x ∈ T, x < Q) :
    let E := T.filter Even
    let O := T.filter fun x => ¬ Even x
    E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1 := by
  classical
  let E := T.filter Even
  let O := T.filter fun x => ¬ Even x
  let D := E.offDiag ∪ O.offDiag
  let code : ℕ × ℕ → ℕ := fun p => (((p.1 : ZMod Q) - p.2).val) / 2
  have hQeven : Even Q := ⟨N, by omega⟩
  have hdisj : Disjoint E.offDiag O.offDiag := by
    rw [Finset.disjoint_left]
    intro p hpE hpO
    have he := Finset.mem_offDiag.mp hpE
    have ho := Finset.mem_offDiag.mp hpO
    exact (Finset.mem_filter.mp ho.1).2 (Finset.mem_filter.mp he.1).2
  have hDcard : D.card =
      (E.card * E.card - E.card) + (O.card * O.card - O.card) := by
    dsimp only [D]
    rw [Finset.card_union_of_disjoint hdisj, Finset.offDiag_card,
      Finset.offDiag_card]
  have hcode_even {p : ℕ × ℕ} (hp : p ∈ D) :
      Even (((p.1 : ZMod Q) - p.2).val) := by
    rcases Finset.mem_union.mp hp with hp | hp
    · have h := Finset.mem_offDiag.mp hp
      exact zmod_sub_val_even (hlt p.1 (Finset.filter_subset _ _ h.1))
        (hlt p.2 (Finset.filter_subset _ _ h.2.1)) hQeven
        (iff_of_true (Finset.mem_filter.mp h.1).2 (Finset.mem_filter.mp h.2.1).2)
    · have h := Finset.mem_offDiag.mp hp
      exact zmod_sub_val_even (hlt p.1 (Finset.filter_subset _ _ h.1))
        (hlt p.2 (Finset.filter_subset _ _ h.2.1)) hQeven
        (iff_of_false (Finset.mem_filter.mp h.1).2 (Finset.mem_filter.mp h.2.1).2)
  have hcode_inj : Set.InjOn code (D : Set (ℕ × ℕ)) := by
    intro p hp r hr heq
    have hevenp := hcode_even hp
    have hevenr := hcode_even hr
    rcases hevenp with ⟨kp, hkp⟩
    rcases hevenr with ⟨kr, hkr⟩
    have hval : (((p.1 : ZMod Q) - p.2).val) =
        (((r.1 : ZMod Q) - r.2).val) := by
      change (((p.1 : ZMod Q) - p.2).val) / 2 =
        (((r.1 : ZMod Q) - r.2).val) / 2 at heq
      omega
    have hdiff : (p.1 : ZMod Q) - p.2 = (r.1 : ZMod Q) - r.2 :=
      ZMod.val_injective Q hval
    have hp' := Finset.mem_union.mp hp
    have hr' := Finset.mem_union.mp hr
    have hpT : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 := by
      rcases hp' with hp' | hp' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').2.1,
          (Finset.mem_offDiag.mp hp').2.2⟩
    have hrT : r.1 ∈ T ∧ r.2 ∈ T ∧ r.1 ≠ r.2 := by
      rcases hr' with hr' | hr' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hr').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hr').2.1,
          (Finset.mem_offDiag.mp hr').2.2⟩
    obtain ⟨h1, h2⟩ := orderedDiff_unique hT hlt hpT.1 hpT.2.1 hrT.1 hrT.2.1
      hpT.2.2 hdiff
    exact Prod.ext h1 h2
  have hcode_mem {p : ℕ × ℕ} (hp : p ∈ D) : code p ∈ Finset.Icc 1 (N - 1) := by
    have hp' := Finset.mem_union.mp hp
    have hpT : p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2 := by
      rcases hp' with hp' | hp' <;> exact
        ⟨Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').1,
          Finset.filter_subset _ _ (Finset.mem_offDiag.mp hp').2.1,
          (Finset.mem_offDiag.mp hp').2.2⟩
    have hne : (p.1 : ZMod Q) - p.2 ≠ 0 := by
      intro hz
      have hz' : (p.1 : ZMod Q) = p.2 := sub_eq_zero.mp hz
      exact hpT.2.2 (Erdos862.eq_of_zmod_eq_of_lt Q p.1 p.2
        (hlt p.1 hpT.1) (hlt p.2 hpT.2.1) hz')
    have hvalpos : 0 < (((p.1 : ZMod Q) - p.2).val) :=
      Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero _).mp hne)
    have hvallt : (((p.1 : ZMod Q) - p.2).val) < 2 * N := by
      rw [← hQeq]
      exact ZMod.val_lt _
    rcases hcode_even hp with ⟨k, hk⟩
    apply Finset.mem_Icc.mpr
    change 1 ≤ (((p.1 : ZMod Q) - p.2).val) / 2 ∧
      (((p.1 : ZMod Q) - p.2).val) / 2 ≤ N - 1
    omega
  have himage : D.image code ⊆ Finset.Icc 1 (N - 1) := by
    rw [Finset.image_subset_iff]
    exact fun p hp => hcode_mem hp
  change E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1
  rw [← hDcard]
  calc
    D.card = (D.image code).card := (Finset.card_image_of_injOn hcode_inj).symm
    _ ≤ (Finset.Icc 1 (N - 1)).card := Finset.card_le_card himage
    _ = N - 1 := by simp

private lemma parity_imbalance_sq {q N a b : ℕ} (hq : 3 ≤ q)
    (hsum : a + b = q) (hN : 2 * N = q * q - 1)
    (hcount : a * a - a + (b * b - b) ≤ N - 1) :
    ((a : ℝ) - b) ^ 2 ≤ 2 * q - 3 := by
  have hqq1 : 1 ≤ q * q := by nlinarith
  have hNpos : 1 ≤ N := by
    have hqq9 : 9 ≤ q * q := by nlinarith
    omega
  have hNR : 2 * (N : ℝ) = (q : ℝ) * q - 1 := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hN
    norm_num only [Nat.cast_mul, Nat.cast_sub hqq1, Nat.cast_one] at hc
    exact hc
  have ha : 1 ≤ a := by
    by_contra hapos
    have ha0 : a = 0 := by omega
    subst a
    have hbq : b = q := by omega
    subst b
    have hqle : q ≤ q * q := by nlinarith
    have hcount' : q * q - q ≤ N - 1 := by simpa using hcount
    have hc : ((q * q - q : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcount'
    rw [Nat.cast_sub hqle, Nat.cast_mul, Nat.cast_sub hNpos] at hc
    norm_num at hc
    nlinarith
  have hb : 1 ≤ b := by
    by_contra hbpos
    have hb0 : b = 0 := by omega
    subst b
    have haq : a = q := by omega
    subst a
    have hqle : q ≤ q * q := by nlinarith
    have hcount' : q * q - q ≤ N - 1 := by simpa using hcount
    have hc : ((q * q - q : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast hcount'
    rw [Nat.cast_sub hqle, Nat.cast_mul, Nat.cast_sub hNpos] at hc
    norm_num at hc
    nlinarith
  have hale : a ≤ a * a := by nlinarith
  have hble : b ≤ b * b := by nlinarith
  have hc : ((a * a - a + (b * b - b) : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hcount
  rw [Nat.cast_add, Nat.cast_sub hale, Nat.cast_sub hble, Nat.cast_sub hNpos,
    Nat.cast_mul, Nat.cast_mul] at hc
  norm_num at hc
  have hs := congrArg (fun n : ℕ => (n : ℝ)) hsum
  norm_num only [Nat.cast_add] at hs
  nlinarith

private def halfShift (x : ℕ) : ℕ := x / 2 + 1

private lemma halfShift_injOn {S : Finset ℕ} {r : ℕ}
    (hpar : ∀ x ∈ S, x % 2 = r) : Set.InjOn halfShift (S : Set ℕ) := by
  intro x hx y hy hxy
  have hxpar := hpar x hx
  have hypar := hpar y hy
  simp only [halfShift] at hxy
  omega

private lemma halfShift_sidon {T S : Finset ℕ} {r : ℕ}
    (hST : S ⊆ T) (hT : IsSidon (T : Set ℕ))
    (hpar : ∀ x ∈ S, x % 2 = r) :
    IsSidon (S.image halfShift : Set ℕ) := by
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ heq
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.mp hi₁
  obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hj₁
  obtain ⟨x₂, hx₂, rfl⟩ := Finset.mem_image.mp hi₂
  obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hj₂
  have horig : x₁ + x₂ = y₁ + y₂ := by
    have hx₁p := hpar x₁ hx₁
    have hx₂p := hpar x₂ hx₂
    have hy₁p := hpar y₁ hy₁
    have hy₂p := hpar y₂ hy₂
    simp only [halfShift] at heq
    omega
  rcases hT x₁ (hST hx₁) y₁ (hST hy₁) x₂ (hST hx₂) y₂ (hST hy₂) horig with h | h
  · exact Or.inl ⟨congrArg halfShift h.1, congrArg halfShift h.2⟩
  · exact Or.inr ⟨congrArg halfShift h.1, congrArg halfShift h.2⟩

private lemma halfShift_bounds {N : ℕ} {S : Finset ℕ}
    (hbound : ∀ x ∈ S, 1 ≤ x ∧ x ≤ 2 * N - 1) :
    S.image halfShift ⊆ Finset.Icc 1 N := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
  have h := hbound x hx
  apply Finset.mem_Icc.mpr
  simp only [halfShift]
  omega

private lemma halfShift_diff_disjoint {Q : ℕ} [NeZero Q]
    {T E O : Finset ℕ} (hET : E ⊆ T) (hOT : O ⊆ T)
    (hTmod : Erdos862.SidonMod Q (T : Set ℕ)) (hlt : ∀ x ∈ T, x < Q)
    (hEpar : ∀ x ∈ E, x % 2 = 0) (hOpar : ∀ x ∈ O, x % 2 = 1)
    (hEne : E.Nonempty) (hOne : O.Nonempty) :
    (E.image halfShift - E.image halfShift) ∩
      (O.image halfShift - O.image halfShift) = ({0} : Finset ℕ) := by
  ext d
  constructor
  · intro hd
    have hdE := (Finset.mem_inter.mp hd).1
    have hdO := (Finset.mem_inter.mp hd).2
    obtain ⟨ae₁, hae₁, ae₂, hae₂, hde⟩ := Finset.mem_sub.mp hdE
    obtain ⟨ao₁, hao₁, ao₂, hao₂, hdo⟩ := Finset.mem_sub.mp hdO
    obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_image.mp hae₁
    obtain ⟨e₂, he₂, rfl⟩ := Finset.mem_image.mp hae₂
    obtain ⟨o₁, ho₁, rfl⟩ := Finset.mem_image.mp hao₁
    obtain ⟨o₂, ho₂, rfl⟩ := Finset.mem_image.mp hao₂
    have he₁p := hEpar e₁ he₁
    have he₂p := hEpar e₂ he₂
    have ho₁p := hOpar o₁ ho₁
    have ho₂p := hOpar o₂ ho₂
    by_cases hd0 : d = 0
    · simpa [hd0]
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hediff : e₁ - e₂ = 2 * d := by
        simp only [halfShift] at hde
        omega
      have hodiff : o₁ - o₂ = 2 * d := by
        simp only [halfShift] at hdo
        omega
      have he12 : e₂ ≤ e₁ := by omega
      have ho12 : o₂ ≤ o₁ := by omega
      have hnatdiff : e₁ - e₂ = o₁ - o₂ := by omega
      have hzcast := congrArg (fun n : ℕ => (n : ZMod Q)) hnatdiff
      have hzdiff : (e₁ : ZMod Q) - e₂ = (o₁ : ZMod Q) - o₂ := by
        simpa [Nat.cast_sub he12, Nat.cast_sub ho12] using hzcast
      obtain ⟨heo, _⟩ := orderedDiff_unique hTmod hlt (hET he₁) (hET he₂)
        (hOT ho₁) (hOT ho₂) (by omega) hzdiff
      omega
  · intro hd
    have hd0 : d = 0 := by simpa using hd
    subst d
    obtain ⟨e, he⟩ := hEne
    obtain ⟨o, ho⟩ := hOne
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_sub.mpr
      exact ⟨halfShift e, Finset.mem_image.mpr ⟨e, he, rfl⟩,
        halfShift e, Finset.mem_image.mpr ⟨e, he, rfl⟩, Nat.sub_self _⟩
    · apply Finset.mem_sub.mpr
      exact ⟨halfShift o, Finset.mem_image.mpr ⟨o, ho, rfl⟩,
        halfShift o, Finset.mem_image.mpr ⟨o, ho, rfl⟩, Nat.sub_self _⟩

private lemma coefficient_comparison {r : ℝ} :
    1 - 3 * r ≤ (1 - r) * (1 - 2 * r) := by
  nlinarith [sq_nonneg r]

private lemma product_lower_bound {r q N m : ℝ} (hrle : r ≤ 1 / 4)
    (hN : 2 * N = q ^ 2 - 1)
    (hprod : ((1 - r) * q / 2) * ((1 - 2 * r) * q / 2) ≤ m * (m - 1)) :
    (1 - 3 * r) * N / 2 ≤ m * (m - 1) := by
  have hcoef : 0 ≤ 1 - 3 * r := by linarith
  have hNq : N / 2 ≤ q ^ 2 / 4 := by nlinarith
  calc
    (1 - 3 * r) * N / 2 = (1 - 3 * r) * (N / 2) := by ring
    _ ≤ (1 - 3 * r) * (q ^ 2 / 4) := mul_le_mul_of_nonneg_left hNq hcoef
    _ ≤ ((1 - r) * (1 - 2 * r)) * (q ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right coefficient_comparison (by positivity)
    _ = ((1 - r) * q / 2) * ((1 - 2 * r) * q / 2) := by ring
    _ ≤ m * (m - 1) := hprod

private lemma choose_two_cast_le_sq (n : ℕ) :
    (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  have htwo : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self n)
  have hc := congrArg (fun k : ℕ => (k : ℝ)) htwo
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    norm_num only [Nat.cast_mul, Nat.cast_sub hn1] at hc
    nlinarith

private lemma coefficient_gap {η : ℝ} (hη : 0 < η) :
    (1 - 7 * η) * (1 + η) ^ 2 < 1 - 3 * (η / 4) := by
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hη3 : 0 ≤ η ^ 2 * η := mul_nonneg hη2 hη.le
  nlinarith

private lemma choose_upper_of_sqrt_bound {n N : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : (n : ℝ) ≤ (1 + ε) * Real.sqrt N) :
    (n.choose 2 : ℝ) ≤ (1 + ε) ^ 2 * (N : ℝ) / 2 := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hrhs : 0 ≤ (1 + ε) * Real.sqrt N := by positivity
  have hsq : (n : ℝ) ^ 2 ≤ ((1 + ε) * Real.sqrt N) ^ 2 :=
    (sq_le_sq₀ hn hrhs).2 h
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)] at hsq
  exact (choose_two_cast_le_sq n).trans (by nlinarith)

private theorem exists_good_pair (q : ℕ) (hqprime : q.Prime) (hq : 3 ≤ q)
    (r : ℝ) (hr : 0 < r) (hrle : r ≤ 1 / 4)
    (hlargeSq : 2 ≤ r ^ 2 * q) (hlargeLin : 4 ≤ r * q) :
    let N := (q ^ 2 - 1) / 2
    ∃ A B : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
      IsSidon (A : Set ℕ) ∧ IsSidon (B : Set ℕ) ∧
      A.card = B.card ∧ (A - A) ∩ (B - B) = {0} ∧
      (1 - 3 * r) * (N : ℝ) / 2 ≤
        ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) := by
  classical
  let Q := q ^ 2 - 1
  let N := Q / 2
  have hqodd : Odd q := hqprime.odd_of_ne_two (by omega)
  have hqq1 : 1 ≤ q * q := by nlinarith
  have hQeven : Even Q := by
    simp only [Q, pow_two]
    apply (Nat.even_sub hqq1).2
    exact iff_of_false (Nat.not_even_iff_odd.mpr (hqodd.mul hqodd)) (by norm_num)
  have hQeq : Q = 2 * N := by
    exact (Nat.two_mul_div_two_of_even hQeven).symm
  have hQgt : 1 < Q := by
    have hqq9 : 9 ≤ q * q := by nlinarith
    simp only [Q, pow_two]
    omega
  letI : NeZero Q := ⟨by omega⟩
  obtain ⟨S, hSsidon, hScard⟩ :
      ∃ S : Finset (ZMod Q), Erdos862.Sidon (S : Set (ZMod Q)) ∧ S.card = q := by
    simpa only [Q] using
      (Erdos862.bose_chowla_at_h_eq_2 q hqprime.isPrimePow)
  have hScardQ : S.card < Q := by
    rw [hScard]
    have hqgap : q + 1 < q * q := by nlinarith
    simp only [Q, pow_two]
    omega
  obtain ⟨S', hS'sidon, hS'card, hS'zero⟩ :=
    Erdos862.shift_sidon_mod Q hQgt S hSsidon hScardQ
  obtain ⟨T, hTmod, hTcard, hTsub, _hTdef⟩ :=
    Erdos862.lift_sidon_mod Q hQgt S' hS'sidon hS'zero
  have hTcardq : T.card = q := hTcard.trans (hS'card.trans hScard)
  have hTlt : ∀ x ∈ T, x < Q := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub hx
    have hx' := Finset.mem_Icc.mp hxmem
    exact lt_of_le_of_lt hx'.2 (Nat.sub_lt (by omega) zero_lt_one)
  have hTsidon : IsSidon (T : Set ℕ) := sidon_of_sidonMod_of_lt hTmod hTlt
  let E := T.filter Even
  let O := T.filter fun x => ¬ Even x
  have hEsumO : E.card + O.card = q := by
    calc
      E.card + O.card = T.card := by
        simpa only [E, O] using
          (Finset.card_filter_add_card_filter_not (s := T) Even)
      _ = q := hTcardq
  have hcount : E.card * E.card - E.card + (O.card * O.card - O.card) ≤ N - 1 :=
    parity_count hQeq hTmod hTlt
  have hNrel : 2 * N = q * q - 1 := by simpa [Q, pow_two] using hQeq.symm
  have himb : (((E.card : ℝ) - O.card) ^ 2) ≤ 2 * q - 3 :=
    parity_imbalance_sq hq hEsumO hNrel hcount
  have hsumR : (E.card : ℝ) + O.card = q := by exact_mod_cast hEsumO
  have hsqdom : 2 * (q : ℝ) ≤ (r * q) ^ 2 := by
    have hqnonneg : (0 : ℝ) ≤ q := by positivity
    have := mul_le_mul_of_nonneg_right hlargeSq hqnonneg
    nlinarith
  have hdiffE : (E.card : ℝ) - O.card ≤ r * q := by
    have hrq : 0 ≤ r * (q : ℝ) := by positivity
    nlinarith [sq_nonneg ((E.card : ℝ) - O.card + r * q)]
  have hdiffO : (O.card : ℝ) - E.card ≤ r * q := by
    have hrq : 0 ≤ r * (q : ℝ) := by positivity
    nlinarith [sq_nonneg ((E.card : ℝ) - O.card - r * q)]
  let m := min E.card O.card
  have hmR : (1 - r) * (q : ℝ) / 2 ≤ (m : ℝ) := by
    by_cases hEO : E.card ≤ O.card
    · rw [show m = E.card by simp [m, hEO]]
      nlinarith
    · have hOE : O.card ≤ E.card := by omega
      rw [show m = O.card by simp [m, hOE]]
      nlinarith
  have hmpos : 0 < m := by
    have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have : (0 : ℝ) < m := by nlinarith
    exact_mod_cast this
  obtain ⟨E', hE'E, hE'card⟩ := Finset.exists_subset_card_eq (min_le_left E.card O.card)
  obtain ⟨O', hO'O, hO'card⟩ := Finset.exists_subset_card_eq (min_le_right E.card O.card)
  have hE'cardm : E'.card = m := hE'card
  have hO'cardm : O'.card = m := hO'card
  have hE'T : E' ⊆ T := hE'E.trans (Finset.filter_subset _ _)
  have hO'T : O' ⊆ T := hO'O.trans (Finset.filter_subset _ _)
  have hE'par : ∀ x ∈ E', x % 2 = 0 := by
    intro x hx
    exact Nat.even_iff.mp (Finset.mem_filter.mp (hE'E hx)).2
  have hO'par : ∀ x ∈ O', x % 2 = 1 := by
    intro x hx
    exact Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (Finset.mem_filter.mp (hO'O hx)).2)
  let A := E'.image halfShift
  let B := O'.image halfShift
  have hAcard : A.card = m := by
    dsimp only [A]
    rw [Finset.card_image_of_injOn (halfShift_injOn hE'par), hE'cardm]
  have hBcard : B.card = m := by
    dsimp only [B]
    rw [Finset.card_image_of_injOn (halfShift_injOn hO'par), hO'cardm]
  have hboundE : ∀ x ∈ E', 1 ≤ x ∧ x ≤ 2 * N - 1 := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub (hE'T hx)
    rw [hQeq] at hxmem
    exact Finset.mem_Icc.mp hxmem
  have hboundO : ∀ x ∈ O', 1 ≤ x ∧ x ≤ 2 * N - 1 := by
    intro x hx
    have hxmem : x ∈ Finset.Icc 1 (Q - 1) := hTsub (hO'T hx)
    rw [hQeq] at hxmem
    exact Finset.mem_Icc.mp hxmem
  have hAsub : A ⊆ Finset.Icc 1 N := by
    exact halfShift_bounds hboundE
  have hBsub : B ⊆ Finset.Icc 1 N := by
    exact halfShift_bounds hboundO
  have hAsidon : IsSidon (A : Set ℕ) := halfShift_sidon hE'T hTsidon hE'par
  have hBsidon : IsSidon (B : Set ℕ) := halfShift_sidon hO'T hTsidon hO'par
  have hE'ne : E'.Nonempty := Finset.card_pos.mp (by rw [hE'cardm]; exact hmpos)
  have hO'ne : O'.Nonempty := Finset.card_pos.mp (by rw [hO'cardm]; exact hmpos)
  have hdiff : (A - A) ∩ (B - B) = ({0} : Finset ℕ) :=
    halfShift_diff_disjoint hE'T hO'T hTmod hTlt hE'par hO'par hE'ne hO'ne
  have hm1R : (1 - 2 * r) * (q : ℝ) / 2 ≤ (m : ℝ) - 1 := by
    nlinarith
  have hleftnonneg : 0 ≤ (1 - r) * (q : ℝ) / 2 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hleftnonneg' : 0 ≤ (1 - 2 * r) * (q : ℝ) / 2 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith
  have hmnonneg : 0 ≤ (m : ℝ) := by positivity
  have hprod : ((1 - r) * (q : ℝ) / 2) * ((1 - 2 * r) * (q : ℝ) / 2) ≤
      (m : ℝ) * ((m : ℝ) - 1) :=
    mul_le_mul hmR hm1R hleftnonneg' hmnonneg
  have hNR : 2 * (N : ℝ) = (q : ℝ) * q - 1 := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) hNrel
    norm_num only [Nat.cast_mul, Nat.cast_sub hqq1, Nat.cast_one] at hc
    exact hc
  have hlower : (1 - 3 * r) * (N : ℝ) / 2 ≤ (m : ℝ) * ((m : ℝ) - 1) := by
    exact product_lower_bound hrle (by simpa [pow_two] using hNR) hprod
  have htwochoose : 2 * m.choose 2 = m * (m - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self m)
  refine ⟨A, B, hAsub, hBsub, hAsidon, hBsidon, hAcard.trans hBcard.symm,
    hdiff, ?_⟩
  rw [hAcard, hBcard]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) htwochoose
  norm_num only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m)] at hc
  norm_num only [Nat.cast_add]
  nlinarith

theorem erdos_43_question_one : ¬
    ∃ C : ℝ, ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C := by
  rintro ⟨C, hC⟩
  ·
    obtain ⟨m : ℕ, hm : C < m⟩ := exists_nat_gt C
    let M := 2 * m + 2
    have hM : 1 ≤ M := by simp [M]
    obtain ⟨N₁, hN₁⟩ := Erdos42.theorem_1_1_via_cayley M hM
    obtain ⟨N₂, hN₂⟩ := (eventually_atTop.1 hC)
    let N := max (max N₁ N₂) 1
    have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN₂' : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hNpos : 1 ≤ N := le_max_right _ _
    let candidates : Finset (Finset ℕ) :=
      (Finset.Icc 1 N).powerset.filter fun A : Finset ℕ ↦ IsSidon (A : Set ℕ)
    have hsingleton : ({1} : Finset ℕ) ∈ candidates := by
      simp [candidates, hNpos, singleton_sidon]
    have hcandidates : candidates.Nonempty := ⟨{1}, hsingleton⟩
    obtain ⟨A, hAcand, hAmax⟩ :=
      Finset.exists_mem_eq_sup candidates hcandidates Finset.card
    have hAsub : A ⊆ Finset.Icc 1 N :=
      Finset.mem_powerset.1 (Finset.mem_filter.1 hAcand).1
    have hAsidon : IsSidon (A : Set ℕ) :=
      (Finset.mem_filter.1 hAcand).2
    have hAcard : A.card = f N := by
      exact hAmax.symm
    have hAone : 1 ≤ A.card := by
      rw [← hAmax]
      exact Finset.le_sup (f := Finset.card) hsingleton
    have hAnonempty : (A : Set ℕ).Nonempty := by
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
      exact ⟨a, ha⟩
    obtain ⟨Bset, hBsub, hBsidon, hBcard, hdiff⟩ :=
      hN₁ N hN₁' (A : Set ℕ) (by
        intro a ha
        exact Finset.mem_Icc.mp (hAsub ha))
        ((isSidon_iff_erdos42 _).1 hAsidon) hAnonempty
    have hBfinite : Bset.Finite := Set.finite_Icc 1 N |>.subset hBsub
    let B : Finset ℕ := hBfinite.toFinset
    have hBsub' : B ⊆ Finset.Icc 1 N := by
      intro b hb
      exact Finset.mem_Icc.mpr (hBsub (by simpa [B] using hb))
    have hBsidon' : IsSidon (B : Set ℕ) := by
      rw [show (B : Set ℕ) = Bset by ext; simp [B]]
      exact (isSidon_iff_erdos42 _).2 hBsidon
    have hBcard' : B.card = M := by
      change hBfinite.toFinset.card = M
      rw [← Set.ncard_eq_toFinset_card Bset hBfinite]
      exact hBcard
    have hdiff' : (A - A) ∩ (B - B) = ({0} : Finset ℕ) := by
      apply Finset.coe_injective
      simpa [B] using hdiff
    have hbound := hN₂ N hN₂' A B hAsub hBsub' hAsidon hBsidon' hdiff'
    rw [hAcard, hBcard'] at hbound
    have hchoose : m < M.choose 2 := by
      rw [show M = (2 * m + 1) + 1 by simp [M]]
      rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
      simp
      omega
    have hchooseR : (m : ℝ) < (M.choose 2 : ℝ) := by exact_mod_cast hchoose
    norm_num only [Nat.cast_add] at hbound
    linarith

theorem erdos_43_question_two : ¬
    ∃ᵉ (c > 0), ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
    ∀ᶠ N in Filter.atTop, ∀ (A B : Finset ℕ),
      A ⊆ Finset.Icc 1 N →
      B ⊆ Finset.Icc 1 N →
      IsSidon (A : Set ℕ) →
      IsSidon (B : Set ℕ) →
      A.card = B.card →
      (A - A) ∩ (B - B) = {0} →
      ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤
        (1 - c + o N) * ((f N).choose 2 : ℝ) := by
  rintro ⟨c, hc, o, ho, hall⟩
  ·
    let η : ℝ := min (c / 8) (1 / 8)
    have hη : 0 < η := by
      dsimp only [η]
      exact lt_min (div_pos hc (by norm_num)) (by norm_num)
    have hηc : η ≤ c / 8 := min_le_left _ _
    have hηle : η ≤ 1 / 8 := min_le_right _ _
    let r : ℝ := η / 4
    have hr : 0 < r := div_pos hη (by norm_num)
    have hrle : r ≤ 1 / 4 := by dsimp only [r]; nlinarith
    obtain ⟨NT, hNT⟩ := Erdos862.ErdosTuran η hη
    have hoevent : ∀ᶠ N : ℕ in atTop, |o N| ≤ η := by
      have h := (Asymptotics.isLittleO_iff.mp ho) hη
      exact h.mono fun N hN => by simpa using hN
    obtain ⟨No, hNo⟩ := eventually_atTop.mp hoevent
    obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hall
    obtain ⟨Lsq : ℕ, hLsq : 2 / r ^ 2 < Lsq⟩ := exists_nat_gt (2 / r ^ 2)
    obtain ⟨Llin : ℕ, hLlin : 4 / r < Llin⟩ := exists_nat_gt (4 / r)
    let R := max NT (max No Nb)
    let Q₀ := max (max Lsq Llin) (2 * R + 3)
    obtain ⟨q, hQq, hqprime⟩ := Nat.exists_infinite_primes Q₀
    have hqR : 2 * R + 3 ≤ q := (le_max_right _ _).trans hQq
    have hq3 : 3 ≤ q := by omega
    have hqLsq : Lsq ≤ q :=
      (le_max_left Lsq Llin).trans (le_max_left _ _ |>.trans hQq)
    have hqLlin : Llin ≤ q :=
      (le_max_right Lsq Llin).trans (le_max_left _ _ |>.trans hQq)
    have hlargeSq : 2 ≤ r ^ 2 * (q : ℝ) := by
      have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
      have hs : 2 < r ^ 2 * (Lsq : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hr2).mp hLsq
      have hcast : (Lsq : ℝ) ≤ q := by exact_mod_cast hqLsq
      nlinarith [mul_le_mul_of_nonneg_left hcast hr2.le]
    have hlargeLin : 4 ≤ r * (q : ℝ) := by
      have hs : 4 < r * (Llin : ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hr).mp hLlin
      have hcast : (Llin : ℝ) ≤ q := by exact_mod_cast hqLlin
      nlinarith [mul_le_mul_of_nonneg_left hcast hr.le]
    let N := (q ^ 2 - 1) / 2
    have hRtwo : R * 2 ≤ q ^ 2 - 1 := by
      have hqR' : 2 * R + 3 ≤ q := hqR
      have haux : R * 2 + 1 ≤ q ^ 2 := by nlinarith
      omega
    have hRN : R ≤ N := by
      dsimp only [N]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 hRtwo
    have hNTN : NT ≤ N := (le_max_left NT (max No Nb)).trans hRN
    have hNoN : No ≤ N :=
      (le_trans (le_max_left No Nb) (le_max_right NT (max No Nb))).trans hRN
    have hNbN : Nb ≤ N :=
      (le_trans (le_max_right No Nb) (le_max_right NT (max No Nb))).trans hRN
    obtain ⟨A, B, hAsub, hBsub, hAsidon, hBsidon, hcard, hdiff, hlower⟩ :=
      exists_good_pair q hqprime hq3 r hr hrle hlargeSq hlargeLin
    have hNpos : 0 < N := by
      have hq9 : 9 ≤ q ^ 2 := by nlinarith
      dsimp only [N]
      omega
    have hoNabs : |o N| ≤ η := hNo N hNoN
    have hoN : o N ≤ η := (le_abs_self (o N)).trans hoNabs
    have hcoefle : 1 - c + o N ≤ 1 - 7 * η := by nlinarith
    have hfbound := hNT N hNTN
    rw [← f_eq_erdos862_f N] at hfbound
    have hfchoose : ((f N).choose 2 : ℝ) ≤ (1 + η) ^ 2 * (N : ℝ) / 2 :=
      choose_upper_of_sqrt_bound hη.le hfbound
    have halleged := hNb N hNbN A B hAsub hBsub hAsidon hBsidon hcard hdiff
    have hleftpos : 0 < ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) := by
      have hcoefpos : 0 < 1 - 3 * r := by
        dsimp only [r]
        nlinarith
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
      have : 0 < (1 - 3 * r) * (N : ℝ) / 2 := by positivity
      exact lt_of_lt_of_le this hlower
    by_cases hcoef : 0 ≤ 1 - c + o N
    · have huppernonneg : 0 ≤ (1 + η) ^ 2 * (N : ℝ) / 2 := by positivity
      have hseven : 0 ≤ 1 - 7 * η := by nlinarith
      have hgap := coefficient_gap hη
      have hNhalf : 0 < (N : ℝ) / 2 := by positivity
      have hstrict :
          (1 - 7 * η) * ((1 + η) ^ 2 * (N : ℝ) / 2) <
            (1 - 3 * r) * (N : ℝ) / 2 := by
        have hg := mul_lt_mul_of_pos_right hgap hNhalf
        dsimp only [r]
        nlinarith
      have hchain :
          ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) <
            (1 - 3 * r) * (N : ℝ) / 2 := calc
        ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ)
            ≤ (1 - c + o N) * ((f N).choose 2 : ℝ) := halleged
        _ ≤ (1 - c + o N) * ((1 + η) ^ 2 * (N : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hfchoose hcoef
        _ ≤ (1 - 7 * η) * ((1 + η) ^ 2 * (N : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hcoefle huppernonneg
        _ < (1 - 3 * r) * (N : ℝ) / 2 := hstrict
      exact (not_lt_of_ge hlower) hchain
    · have hcoefneg : 1 - c + o N < 0 := lt_of_not_ge hcoef
      have hchoose_nonneg : (0 : ℝ) ≤ ((f N).choose 2 : ℝ) := by positivity
      have : (1 - c + o N) * ((f N).choose 2 : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hcoefneg.le hchoose_nonneg
      linarith

end

section
open Filter Pointwise

/-- **Erdős Problem 43.** Both questions on erdosproblems.com have a negative answer: the
`O(1)` bound fails, and so does the improved `(1 - c + o(1))` bound in the equal-cardinality
case. -/
theorem erdos_43 :
    (¬ ∃ C : ℝ, ∀ᶠ N in atTop, ∀ (A B : Finset ℕ),
        A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        IsSidon (A : Set ℕ) → IsSidon (B : Set ℕ) →
        (A - A) ∩ (B - B) = {0} →
        ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤ ((f N).choose 2 : ℝ) + C) ∧
      (¬ ∃ᵉ (c > 0), ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
        ∀ᶠ N in atTop, ∀ (A B : Finset ℕ),
          A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
          IsSidon (A : Set ℕ) → IsSidon (B : Set ℕ) →
          A.card = B.card →
          (A - A) ∩ (B - B) = {0} →
          ((A.card.choose 2 + B.card.choose 2 : ℕ) : ℝ) ≤
            (1 - c + o N) * ((f N).choose 2 : ℝ)) :=
  ⟨erdos_43_question_one, erdos_43_question_two⟩

end

#print axioms erdos_43
-- 'Erdos43.erdos_43' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos43
