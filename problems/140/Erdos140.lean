import Mathlib

set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedVariables false

namespace Erdos140

/-
# Problem Description

Erdős Problem 140 ($500). Let `r₃(N)` be the size of the largest subset of `{1, …, N}`
containing no non-trivial 3-term arithmetic progression. Show that `r₃(N) ≪ N / (log N)^C`
for every `C > 0`. `erdos_140` proves this. It is a theorem of Kelley and Meka.

Erdős and Graham conjectured the same for `k`-term progressions; that remains open.

`r3 N` is `addRothNumber (Finset.Icc 1 N)`, so progression-freeness is Mathlib's own
notion, and `r3_eq_rothNumberNat` records that this interval convention agrees with
Mathlib's `rothNumberNat`. The `≪` is `Asymptotics.IsBigO` along `atTop`, with `C`
universally quantified outside.
-/

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Counting.lean` -/

section
/-!
# Elementary counting and cyclic-embedding lemmas for Erdős Problem 140

This file contains only the finite combinatorial bookkeeping used when passing
between an interval of natural numbers and the odd cyclic group `ZMod (2 * N + 1)`.
-/

open _root_.Finset _root_.Function

section ThreeAPCount

variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

/-- The number of ordered triples `(a,b,c) ∈ A³` satisfying `a + c = b + b`. -/
def threeAPCount (A : Finset α) : ℕ :=
  #(((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2)

@[simp]
lemma mem_threeAPCountFinset {A : Finset α} {a b c : α} :
    ((a, b), c) ∈ (((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) ↔
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
  simp [and_assoc]

variable [IsCancelAdd α]

/-- A three-term-progression-free finite set has exactly its diagonal ordered
solutions to `a + c = b + b`. -/
theorem threeAPCount_eq_card {A : Finset α} (hA : ThreeAPFree (A : Set α)) :
    threeAPCount A = #A := by
  classical
  let D : Finset ((α × α) × α) := A.image fun a ↦ ((a, a), a)
  have hfilter :
      (((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) = D := by
    ext x
    rcases x with ⟨⟨a, b⟩, c⟩
    simp only [mem_filter, mem_product, D, mem_image]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hc⟩, habc⟩
      have hab : a = b := hA ha hb hc habc
      have hbc : b = c := hA.eq_right ha hb hc habc
      exact ⟨b, hb, by simp [hab, hbc]⟩
    · rintro ⟨d, hd, hdiag⟩
      have hda : d = a := congrArg (fun x ↦ x.1.1) hdiag
      have hdb : d = b := congrArg (fun x ↦ x.1.2) hdiag
      have hdc : d = c := congrArg (fun x ↦ x.2) hdiag
      subst a
      subst b
      subst c
      simp [hd]
  change #(((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) = #A
  rw [hfilter]
  change #(A.image fun a ↦ ((a, a), a)) = #A
  rw [card_image_of_injective]
  intro a b hab
  exact congrArg (fun x ↦ x.1.1) hab

end ThreeAPCount

section CyclicEmbedding

/-- The odd modulus used to embed `[1,N]` without wraparound of two-term sums. -/
abbrev intervalModulus (N : ℕ) : ℕ := 2 * N + 1

/-- The standard embedding of natural numbers into the odd cyclic group of order `2N+1`. -/
abbrev intervalEmbedding (N : ℕ) (a : ℕ) : ZMod (intervalModulus N) := a

/-- Casting to `ZMod (2N+1)` is injective on numbers at most `N`. -/
theorem intervalEmbedding_injOn (N : ℕ) :
    Set.InjOn (intervalEmbedding N) (Set.Iic N) := by
  intro a ha b hb hab
  change a ≤ N at ha
  change b ≤ N at hb
  have ha_lt : a < intervalModulus N := by
    change a < 2 * N + 1
    omega
  have hb_lt : b < intervalModulus N := by
    change b < 2 * N + 1
    omega
  have hmod :=
    (ZMod.natCast_eq_natCast_iff' a b (intervalModulus N)).mp hab
  rwa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod

/-- Equality of two sums in `ZMod (2N+1)` reflects equality in `ℕ` when all
four summands are at most `N`. -/
theorem intervalEmbedding_add_eq_add_iff {N a b c d : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    intervalEmbedding N a + intervalEmbedding N c =
        intervalEmbedding N b + intervalEmbedding N d ↔
      a + c = b + d := by
  constructor
  · intro h
    have hcast : ((a + c : ℕ) : ZMod (intervalModulus N)) =
        ((b + d : ℕ) : ZMod (intervalModulus N)) := by
      simpa only [Nat.cast_add] using h
    have hac_lt : a + c < intervalModulus N := by
      change a + c < 2 * N + 1
      omega
    have hbd_lt : b + d < intervalModulus N := by
      change b + d < 2 * N + 1
      omega
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (a + c) (b + d) (intervalModulus N)).mp hcast
    rwa [Nat.mod_eq_of_lt hac_lt, Nat.mod_eq_of_lt hbd_lt] at hmod
  · intro h
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ ↦ (n : ZMod (intervalModulus N))) h

/-- The finite-set image of `A ⊆ ℕ` in `ZMod (2N+1)`. -/
def intervalImage (N : ℕ) (A : Finset ℕ) : Finset (ZMod (intervalModulus N)) :=
  A.image (intervalEmbedding N)

@[simp]
theorem mem_intervalImage {N : ℕ} {A : Finset ℕ} {x : ZMod (intervalModulus N)} :
    x ∈ intervalImage N A ↔ ∃ a ∈ A, intervalEmbedding N a = x := by
  simp [intervalImage]

/-- Embedding a set contained in `[0,N]` preserves its cardinality. -/
theorem card_intervalImage {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) : #(intervalImage N A) = #A := by
  rw [intervalImage, card_image_iff]
  exact fun a ha b hb h ↦ intervalEmbedding_injOn N (hA a ha) (hA b hb) h

/-- The no-wrap embedding preserves the number of all ordered three-term
progressions, not only the diagonal count in an AP-free set. -/
theorem threeAPCount_intervalImage {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) :
    threeAPCount (intervalImage N A) = threeAPCount A := by
  classical
  let f : ((ℕ × ℕ) × ℕ) → ((ZMod (intervalModulus N) × ZMod (intervalModulus N)) ×
      ZMod (intervalModulus N)) := fun x ↦
    ((intervalEmbedding N x.1.1, intervalEmbedding N x.1.2), intervalEmbedding N x.2)
  let T : Finset ((ℕ × ℕ) × ℕ) :=
    ((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2
  let U : Finset ((ZMod (intervalModulus N) × ZMod (intervalModulus N)) ×
      ZMod (intervalModulus N)) :=
    (((intervalImage N A ×ˢ intervalImage N A) ×ˢ intervalImage N A).filter fun x ↦
      x.1.1 + x.2 = x.1.2 + x.1.2)
  have hUT : U = T.image f := by
    ext x
    rcases x with ⟨⟨x, y⟩, z⟩
    constructor
    · intro hxyz
      have hxyz' :
          x ∈ intervalImage N A ∧ y ∈ intervalImage N A ∧ z ∈ intervalImage N A ∧
            x + z = y + y := by
        simpa [U, and_assoc] using hxyz
      rcases hxyz' with ⟨hx, hy, hz, hrel⟩
      obtain ⟨a, ha, rfl⟩ := mem_intervalImage.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_intervalImage.mp hy
      obtain ⟨c, hc, rfl⟩ := mem_intervalImage.mp hz
      refine mem_image.mpr ⟨((a, b), c), ?_, rfl⟩
      have habc : a + c = b + b :=
        (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).1 hrel
      simp [T, ha, hb, hc, habc]
    · intro hxyz
      obtain ⟨⟨⟨a, b⟩, c⟩, habc_mem, habc_eq⟩ := mem_image.mp hxyz
      have habc' : a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
        simpa [T, and_assoc] using habc_mem
      rcases habc' with ⟨ha, hb, hc, habc⟩
      have hx : intervalEmbedding N a ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨a, ha, rfl⟩
      have hy : intervalEmbedding N b ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨b, hb, rfl⟩
      have hz : intervalEmbedding N c ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨c, hc, rfl⟩
      have hrel : intervalEmbedding N a + intervalEmbedding N c =
          intervalEmbedding N b + intervalEmbedding N b :=
        (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).2 habc
      rw [← habc_eq]
      simp [U, f, hx, hy, hz, hrel]
  have hf : Set.InjOn f T := by
    rintro ⟨⟨a, b⟩, c⟩ habc ⟨⟨a', b'⟩, c'⟩ habc' heq
    have habc_mem : a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
      simpa [T, and_assoc] using habc
    have habc_mem' : a' ∈ A ∧ b' ∈ A ∧ c' ∈ A ∧ a' + c' = b' + b' := by
      simpa [T, and_assoc] using habc'
    rcases habc_mem with ⟨ha, hb, hc, -⟩
    rcases habc_mem' with ⟨ha', hb', hc', -⟩
    have haa : a = a' := intervalEmbedding_injOn N (hA a ha) (hA a' ha') <|
      congrArg (fun x ↦ x.1.1) heq
    have hbb : b = b' := intervalEmbedding_injOn N (hA b hb) (hA b' hb') <|
      congrArg (fun x ↦ x.1.2) heq
    have hcc : c = c' := intervalEmbedding_injOn N (hA c hc) (hA c' hc') <|
      congrArg (fun x ↦ x.2) heq
    simp [haa, hbb, hcc]
  change #U = #T
  rw [hUT, card_image_of_injOn hf]

end CyclicEmbedding

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Endpoint.lean` -/

section
/-!
# The endpoint of Erdős Problem 140

This file identifies the literal extremal function on `{1, ..., N}` with
Mathlib's `rothNumberNat`, and records the elementary analytic implication
from a stretched-exponential Kelley--Meka bound to every logarithmic saving.
-/

open _root_.Filter _root_.Finset
open scoped _root_.Topology

/-- The largest cardinality of a three-term-progression-free subset of
`{1, ..., N}`. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  addRothNumber (Finset.Icc 1 N)

/-- The interval convention in `r3` agrees exactly with Mathlib's convention
`rothNumberNat N = addRothNumber (range N)`. -/
theorem r3_eq_rothNumberNat (N : ℕ) : r3 N = rothNumberNat N := by
  rw [r3, ← Finset.Ico_add_one_right_eq_Icc, addRothNumber_Ico]
  simp

/-- A positive stretched exponential in `log N` beats every fixed real power
of `log N`.  This is the analytic core of the last step in Problem 140. -/
theorem tendsto_log_rpow_mul_stretchedExp
    {c beta : ℝ} (hc : 0 < c) (hbeta : 0 < beta) (C : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (Real.log (N : ℝ)) ^ C *
          Real.exp (-c * (Real.log (N : ℝ)) ^ beta))
      atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ beta) atTop atTop :=
    (tendsto_rpow_atTop hbeta).comp hlog
  have h :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C / beta) c hc).comp hpow
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with N hN
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN.le)
  change
    ((Real.log (N : ℝ)) ^ beta) ^ (C / beta) *
        Real.exp (-c * (Real.log (N : ℝ)) ^ beta) =
      (Real.log (N : ℝ)) ^ C *
        Real.exp (-c * (Real.log (N : ℝ)) ^ beta)
  congr 1
  rw [← Real.rpow_mul hlog_nonneg]
  congr 1
  field_simp [hbeta.ne']

/-- Eventual Kelley--Meka decay implies the exact `IsBigO` conclusion used in
Erdős Problem 140.  Constants `K`, `c`, and `beta` are independent of `N`;
the Kelley--Meka theorem supplies positive `c` and `beta` (in particular one
may take `beta = 1 / 12`). -/
theorem isBigO_r3_log_rpow_of_stretchedExp
    {K c beta : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hbeta : 0 < beta)
    (hKM : ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤
        K * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ beta))
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  have hdecay :=
    tendsto_log_rpow_mul_stretchedExp hc hbeta C
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (Real.log (N : ℝ)) ^ C *
          Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤ 1 :=
    hdecay.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [hKM, hsmall, eventually_gt_atTop 1] with N hbound hsmallN hN
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hlogpow_pos : 0 < (Real.log (N : ℝ)) ^ C :=
    Real.rpow_pos_of_pos hlog_pos C
  rw [Real.norm_of_nonneg (Nat.cast_nonneg (r3 N))]
  rw [Real.norm_of_nonneg (div_nonneg hN_nonneg hlogpow_pos.le)]
  apply hbound.trans
  have hexp_le :
      Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤
        1 / (Real.log (N : ℝ)) ^ C := by
    rw [le_div_iff₀ hlogpow_pos]
    simpa [mul_comm] using hsmallN
  calc
    K * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ beta) ≤
        K * (N : ℝ) * (1 / (Real.log (N : ℝ)) ^ C) :=
      mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hK hN_nonneg)
    _ = K * ((N : ℝ) / (Real.log (N : ℝ)) ^ C) := by ring

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Quantitative.lean` -/

section
/-!
# Quantitative ordered counting implies the Erdős 140 bound

The Kelley--Meka input is isolated below in the form in which its constants
are used.  A set of density at least `2⁻ᵈ` has at least
`exp (-K d^12) N^2` ordered three-term progressions.  The logarithmic
hypothesis in the definition is the equivalent, division-free-in-the-density
form `log (N / |A|) ≤ d log 2`; nonemptiness makes this equivalence honest.

The proofs in this file are elementary.  They choose an extremal AP-free set,
observe that its ordered progressions are precisely the diagonal ones, and
choose `d = ceil (log (N / |A|) / log 2)`.  Taking logarithms then gives a
stretched-exponential upper bound for `r3`.
-/

open _root_.Filter _root_.Finset
open scoped _root_.Topology

/-- The explicit quantitative ordered-count statement supplied by the
Kelley--Meka theorem (with an absolute constant and a harmless threshold).

The count includes all ordered triples `(a,b,c)` satisfying `a+c=2b`, so the
diagonal solutions are included. -/
def KelleyMekaOrderedCountHypothesis (K : ℝ) (N₀ : ℕ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), N₀ ≤ N →
      ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 N → A.Nonempty →
        ∀ d : ℕ,
          1 ≤ d →
          Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2 →
            Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤
              (threeAPCount A : ℝ)

/-- The ordered-count hypothesis forces the Kelley--Meka
stretched-exponential bound for the literal extremal function `r3`.

The constants are explicit: the exponent is `1/12`, and the decay constant is
`log 2 / (2 * K^(1/12))`. -/
theorem eventually_r3_le_stretchedExp_of_orderedCount
    {K : ℝ} {N₀ : ℕ} (hKM : KelleyMekaOrderedCountHypothesis K N₀) :
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤
        (N : ℝ) * Real.exp
          (-(Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) := by
  have hK : 0 < K := hKM.1
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog_div : Tendsto (fun N : ℕ => Real.log (N : ℝ) / K) atTop atTop :=
    Tendsto.atTop_div_const hK hlog
  have hroot :
      Tendsto
        (fun N : ℕ => (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hlog_div
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 3,
      hroot.eventually_ge_atTop 2] with N hNN₀ hN hroot_large
  obtain ⟨A, hAIcc, hAcard, hAfree⟩ := addRothNumber_spec (Finset.Icc 1 N)
  have hAcard' : #A = r3 N := by simpa [r3] using hAcard
  have hr3_le_nat : r3 N ≤ N := by
    rw [r3_eq_rothNumberNat]
    exact rothNumberNat_le N
  have hr3_pos : 0 < r3 N := by
    have hsingleton : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N := by
      simpa using (show 1 ≤ N by omega)
    have hmono := addRothNumber.mono hsingleton
    have hmono' : 1 ≤ addRothNumber (Finset.Icc 1 N) := by simpa using hmono
    have : 0 < addRothNumber (Finset.Icc 1 N) := by omega
    simpa [r3] using this
  have hAne : A.Nonempty := by
    apply Finset.card_pos.mp
    simpa [hAcard'] using hr3_pos
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hr3_pos_real : (0 : ℝ) < r3 N := by exact_mod_cast hr3_pos
  have hr3_le_real : (r3 N : ℝ) ≤ N := by exact_mod_cast hr3_le_nat
  have hratio_one : (1 : ℝ) ≤ (N : ℝ) / (r3 N : ℝ) := by
    rw [one_le_div hr3_pos_real]
    exact hr3_le_real
  have hratio_pos : (0 : ℝ) < (N : ℝ) / (r3 N : ℝ) :=
    div_pos hN_pos hr3_pos_real
  let q : ℝ := Real.log ((N : ℝ) / (r3 N : ℝ)) / Real.log 2
  let d : ℕ := Nat.ceil q
  have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg (Real.log_nonneg hratio_one) hlog_two.le
  have hlog_density :
      Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2 := by
    rw [hAcard']
    rw [← div_le_iff₀ hlog_two]
    simpa [q, d] using Nat.le_ceil q
  have hr3_lt_nat : r3 N < N := by
    apply lt_of_le_of_ne hr3_le_nat
    intro heq
    have hcard_Icc : #(Finset.Icc 1 N) = N := by
      rw [Nat.card_Icc]
      omega
    have hAeq : A = Finset.Icc 1 N := by
      apply Finset.eq_of_subset_of_card_le hAIcc
      rw [hcard_Icc, hAcard', heq]
    have hfree_Icc : ThreeAPFree (Finset.Icc 1 N : Set ℕ) := by
      simpa [hAeq] using hAfree
    have hbad := hfree_Icc (a := 1) (b := 2) (c := 3)
      (by simp [show 1 ≤ N by omega]) (by simp [show 2 ≤ N by omega])
      (by simp [show 3 ≤ N by omega]) (by norm_num)
    omega
  have hq_pos : 0 < q := by
    have hratio_gt : (1 : ℝ) < (N : ℝ) / (r3 N : ℝ) := by
      rw [lt_div_iff₀ hr3_pos_real]
      norm_num
      exact_mod_cast hr3_lt_nat
    exact div_pos (Real.log_pos hratio_gt) hlog_two
  have hd_one : 1 ≤ d := by
    exact (Nat.ceil_pos.mpr hq_pos)
  have hcount := hKM.2 N hNN₀ A hAIcc hAne d hd_one hlog_density
  rw [threeAPCount_eq_card hAfree, hAcard'] at hcount
  have hcountN :
      Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤ (N : ℝ) :=
    hcount.trans hr3_le_real
  have hdecay_mul_N :
      Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ) ≤ 1 := by
    have hscaled :
        (Real.exp (-K * (d : ℝ) ^ 12) * (N : ℝ)) * (N : ℝ) ≤
          1 * (N : ℝ) := by
      simpa [pow_two, mul_assoc] using hcountN
    exact (le_of_mul_le_mul_right hscaled hN_pos)
  have hlog_bound : Real.log (N : ℝ) ≤ K * (d : ℝ) ^ 12 := by
    have hlog_ineq :=
      Real.log_le_log
        (mul_pos (Real.exp_pos _) hN_pos)
        hdecay_mul_N
    rw [Real.log_mul (Real.exp_ne_zero _) hN_pos.ne', Real.log_exp,
      Real.log_one] at hlog_ineq
    linarith
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hdiv_nonneg : 0 ≤ Real.log (N : ℝ) / K :=
    div_nonneg hlog_nonneg hK.le
  have hdiv_le_pow : Real.log (N : ℝ) / K ≤ (d : ℝ) ^ 12 := by
    rw [div_le_iff₀ hK]
    simpa [mul_comm] using hlog_bound
  have hroot_le_d :
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤ (d : ℝ) := by
    calc
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤
          ((d : ℝ) ^ 12) ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow hdiv_nonneg hdiv_le_pow (by norm_num)
      _ = (d : ℝ) := by
        convert Real.pow_rpow_inv_natCast (show (0 : ℝ) ≤ d by positivity)
          (by norm_num : (12 : ℕ) ≠ 0) using 1
        all_goals norm_num
  have hceil_upper : (d : ℝ) < q + 1 := by
    simpa [d] using Nat.ceil_lt_add_one hq_nonneg
  have hhalf_root_le_q :
      (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) / 2 ≤ q := by
    linarith
  have hlog_ratio_lower :
      (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) ≤
        Real.log ((N : ℝ) / (r3 N : ℝ)) := by
    calc
      (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) =
          ((Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) / 2) * Real.log 2 := by ring
      _ ≤ q * Real.log 2 :=
        mul_le_mul_of_nonneg_right hhalf_root_le_q hlog_two.le
      _ = Real.log ((N : ℝ) / (r3 N : ℝ)) := by
        simp [q, hlog_two.ne']
  have hKroot_pos : 0 < K ^ (1 / 12 : ℝ) :=
    Real.rpow_pos_of_pos hK _
  have hcoefficient :
      (Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
          (Real.log (N : ℝ)) ^ (1 / 12 : ℝ) =
        (Real.log 2 / 2) *
          (Real.log (N : ℝ) / K) ^ (1 / 12 : ℝ) := by
    rw [Real.div_rpow hlog_nonneg hK.le]
    field_simp [hKroot_pos.ne']
  have hexp_le_ratio :
      Real.exp
          ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) ≤
        (N : ℝ) / (r3 N : ℝ) := by
    rw [← Real.le_log_iff_exp_le hratio_pos]
    rw [hcoefficient]
    exact hlog_ratio_lower
  have hmul_exp_le :
      (r3 N : ℝ) *
          Real.exp
            ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
              (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) ≤
        (N : ℝ) := by
    have := (le_div_iff₀ hr3_pos_real).mp hexp_le_ratio
    simpa [mul_comm] using this
  calc
    (r3 N : ℝ) ≤
        (N : ℝ) /
          Real.exp
            ((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
              (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) :=
      (le_div_iff₀ (Real.exp_pos _)).2 hmul_exp_le
    _ = (N : ℝ) *
        Real.exp
          (-((Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
            (Real.log (N : ℝ)) ^ (1 / 12 : ℝ))) := by
      rw [Real.exp_neg, div_eq_mul_inv]
    _ = (N : ℝ) * Real.exp
        (-(Real.log 2 / (2 * K ^ (1 / 12 : ℝ))) *
          (Real.log (N : ℝ)) ^ (1 / 12 : ℝ)) := by
      congr 2
      ring

/-- The ordered-count hypothesis yields every logarithmic saving in the exact
`IsBigO` form used by Erdős Problem 140. -/
theorem isBigO_r3_log_rpow_of_orderedCount
    {K : ℝ} {N₀ : ℕ} (hKM : KelleyMekaOrderedCountHypothesis K N₀)
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  have hc : 0 < Real.log 2 / (2 * K ^ (1 / 12 : ℝ)) := by
    exact div_pos (Real.log_pos (by norm_num))
      (mul_pos two_pos (Real.rpow_pos_of_pos hKM.1 _))
  apply isBigO_r3_log_rpow_of_stretchedExp
      (K := 1) (c := Real.log 2 / (2 * K ^ (1 / 12 : ℝ)))
      (beta := (1 / 12 : ℝ)) zero_le_one hc (by norm_num) _ C
  simpa using eventually_r3_le_stretchedExp_of_orderedCount hKM

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/DensityIteration.lean` -/

section
/-!
# Quantitative density-iteration bookkeeping for Erdős Problem 140

This file isolates the finite recursion used after the analytic input in a
Bloom--Sisask/Kelley--Meka argument has supplied a count-or-increment lemma.
It deliberately does not assert that analytic input.  Instead,
`OneStepHypothesis` records it as a hypothesis and `count_of_oneStep` proves
that it can be iterated only finitely often.

The bookkeeping keeps the three quantities that change in an iteration:
the relative density, the rank of the ambient Bohr set, and its cardinality.
At an increment the density grows by a fixed factor, the rank grows by at most
`rankCost`, and the cardinality loses at most the factor `exp (-sizeCost)`.
The conclusion pays for every possible cardinality loss.  The final theorem
specializes to a dyadic density scale and turns an eleventh-power loss at each
of at most `L + 1` stages into the expected twelfth-power exponent.
-/

namespace DensityIteration

noncomputable section

/-- The numerical data retained at one stage of a density iteration.

`card` is the cardinality of the current finite ambient Bohr set.  We keep it
as a natural number, and cast it to `ℝ` only in analytic inequalities. -/
structure State where
  density : ℝ
  rank : ℕ
  card : ℕ

/-- A single legitimate density-increment move. -/
def IsIncrement (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (s t : State) : Prop :=
  0 ≤ t.density ∧
    q * s.density ≤ t.density ∧
    t.density ≤ 1 ∧
    t.rank ≤ s.rank + rankCost ∧
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- The local lower bound for the configuration count at a state. -/
def HasCount (cost count : ℝ) (s : State) : Prop :=
  Real.exp (-cost) * (s.card : ℝ) ^ 2 ≤ count

/-- The abstract analytic input to the density iteration.

Every state of density at most one either already has the desired local
configuration count, or admits a controlled density-increment move. -/
def OneStepHypothesis (q : ℝ) (rankCost : ℕ)
    (sizeCost localCost count : ℝ) : Prop :=
  ∀ s : State, 0 ≤ s.density → s.density ≤ 1 →
    HasCount localCost count s ∨
      ∃ t : State, IsIncrement q rankCost sizeCost s t

private lemma square_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy),
    mul_nonneg hy (sub_nonneg.mpr hxy)]

/-- **Finite count-or-increment recursion.**

If `q ^ fuel * density > 1`, `fuel` consecutive increment moves are
impossible because every admissible state has density at most one.  Thus a
count alternative occurs.  The exponent in the returned bound includes two
copies of every possible size loss, since the configuration count is
quadratic in the ambient cardinality. -/
theorem count_of_oneStep
    {q : ℝ} {rankCost fuel : ℕ} {sizeCost localCost count : ℝ}
    (hq : 0 ≤ q) (hsizeCost : 0 ≤ sizeCost) (_hlocalCost : 0 ≤ localCost)
    (hstep : OneStepHypothesis q rankCost sizeCost localCost count)
    (s : State) (hs0 : 0 ≤ s.density) (hs1 : s.density ≤ 1)
    (hgrowth : 1 < q ^ fuel * s.density) :
    HasCount (localCost + 2 * (fuel : ℝ) * sizeCost) count s := by
  induction fuel generalizing s with
  | zero =>
      simp only [Nat.cast_zero, pow_zero, one_mul, mul_zero] at hgrowth ⊢
      exact (not_lt_of_ge hs1 hgrowth).elim
  | succ fuel ih =>
      rcases hstep s hs0 hs1 with hcount | ⟨t, ht⟩
      · have hcost : localCost ≤
            localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost := by
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsizeCost)
        have hexp : Real.exp
              (-(localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost)) ≤
            Real.exp (-localCost) :=
          Real.exp_le_exp.mpr (neg_le_neg hcost)
        exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg (s.card : ℝ))).trans hcount
      · have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq _
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left ht.2.1 hqpow
        have hrec := ih t ht.1 ht.2.2.1 hgrowth'
        have hscaled0 : 0 ≤ Real.exp (-sizeCost) * (s.card : ℝ) := by positivity
        have hsquare :
            (Real.exp (-sizeCost) * (s.card : ℝ)) ^ 2 ≤ (t.card : ℝ) ^ 2 :=
          square_mono hscaled0 ht.2.2.2.2
        have hfactor0 : 0 ≤
            Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) :=
          (Real.exp_pos _).le
        have hloss :
            Real.exp
                (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) *
                (s.card : ℝ) ^ 2 ≤
              Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                (t.card : ℝ) ^ 2 := by
          have hexp :
              Real.exp
                  (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) =
                Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                  Real.exp (-sizeCost) ^ 2 := by
            rw [pow_two, ← Real.exp_add, ← Real.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp]
          rw [mul_assoc, ← mul_pow]
          exact mul_le_mul_of_nonneg_left hsquare hfactor0
        exact hloss.trans hrec

/-- The dyadic logarithmic scale used for an initial density. -/
def OnDyadicScale (L : ℕ) (density : ℝ) : Prop :=
  1 / (2 : ℝ) ^ L ≤ density

end

end DensityIteration

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/ReachableIteration.lean` -/

section
/-!
# Reachability-restricted density iteration for Erdős Problem 140

The unrestricted `DensityIteration.OneStepHypothesis` is useful as a purely
logical bookkeeping interface, but its quantifier over every numerical state
is too strong for a concrete finite ambient problem: states with arbitrarily
large `card` need not arise from the initial Bohr set.

This file supplies the interface used by the analytic assembly.  Its
`Reachable` predicate is rooted at one specified initial state.  Every edge is
a controlled density increment and every reached cardinality is bounded by
the initial cardinality.  Consequently `OneStepHypothesis` asks for the
analytic count-or-increment alternative only at states that can actually be
produced by the iteration.  The finite recursion and its twelfth-power
specialization retain the exact same loss calculation.
-/

namespace ReachableIteration

noncomputable section

open Erdos140.DensityIteration

/-- A state obtained from `initial` by a finite chain of legitimate increment
moves, with every new ambient cardinality bounded by the initial one. -/
inductive Reachable (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (initial : State) : State → Prop
  | root : Reachable q rankCost sizeCost initial initial
  | step {s t : State} :
      Reachable q rankCost sizeCost initial s →
      IsIncrement q rankCost sizeCost s t →
      t.card ≤ initial.card →
      Reachable q rankCost sizeCost initial t

/-- The analytic input restricted to the cone reachable from `initial`.

In the increment alternative the returned cardinality bound makes the new
state reachable, so the same hypothesis is available at the following
recursive call. -/
def OneStepHypothesis (q : ℝ) (rankCost : ℕ)
    (sizeCost localCost count : ℝ) (initial : State) : Prop :=
  ∀ s : State, Reachable q rankCost sizeCost initial s →
    0 ≤ s.density → s.density ≤ 1 →
      HasCount localCost count s ∨
        ∃ t : State,
          IsIncrement q rankCost sizeCost s t ∧ t.card ≤ initial.card

private lemma square_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := hx.trans hxy
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hxy),
    mul_nonneg hy (sub_nonneg.mpr hxy)]

/-- Finite count-or-increment recursion on the reachable cone.

The returned exponent includes two copies of every possible logarithmic size
loss, because the configuration count is quadratic in the ambient
cardinality. -/
theorem count_of_oneStep
    {q : ℝ} {rankCost fuel : ℕ} {sizeCost localCost count : ℝ}
    {initial : State}
    (hq : 0 ≤ q) (hsizeCost : 0 ≤ sizeCost) (_hlocalCost : 0 ≤ localCost)
    (hstep : OneStepHypothesis q rankCost sizeCost localCost count initial)
    (s : State) (hsReachable : Reachable q rankCost sizeCost initial s)
    (hs0 : 0 ≤ s.density) (hs1 : s.density ≤ 1)
    (hgrowth : 1 < q ^ fuel * s.density) :
    HasCount (localCost + 2 * (fuel : ℝ) * sizeCost) count s := by
  induction fuel generalizing s with
  | zero =>
      simp only [Nat.cast_zero, pow_zero, one_mul, mul_zero] at hgrowth ⊢
      exact (not_lt_of_ge hs1 hgrowth).elim
  | succ fuel ih =>
      rcases hstep s hsReachable hs0 hs1 with hcount | ⟨t, ht, htCard⟩
      · have hcost : localCost ≤
            localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost := by
          exact le_add_of_nonneg_right
            (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsizeCost)
        have hexp : Real.exp
              (-(localCost + 2 * ((fuel + 1 : ℕ) : ℝ) * sizeCost)) ≤
            Real.exp (-localCost) :=
          Real.exp_le_exp.mpr (neg_le_neg hcost)
        exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg (s.card : ℝ))).trans hcount
      · have htReachable : Reachable q rankCost sizeCost initial t :=
          Reachable.step hsReachable ht htCard
        have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq _
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left ht.2.1 hqpow
        have hrec := ih t htReachable ht.1 ht.2.2.1 hgrowth'
        have hscaled0 : 0 ≤ Real.exp (-sizeCost) * (s.card : ℝ) := by
          positivity
        have hsquare :
            (Real.exp (-sizeCost) * (s.card : ℝ)) ^ 2 ≤ (t.card : ℝ) ^ 2 :=
          square_mono hscaled0 ht.2.2.2.2
        have hfactor0 : 0 ≤
            Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) :=
          (Real.exp_pos _).le
        have hloss :
            Real.exp
                (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) *
                (s.card : ℝ) ^ 2 ≤
              Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                (t.card : ℝ) ^ 2 := by
          have hexp :
              Real.exp
                  (-(localCost + 2 * (((fuel + 1 : ℕ) : ℝ)) * sizeCost)) =
                Real.exp (-(localCost + 2 * (fuel : ℝ) * sizeCost)) *
                  Real.exp (-sizeCost) ^ 2 := by
            rw [pow_two, ← Real.exp_add, ← Real.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp]
          rw [mul_assoc, ← mul_pow]
          exact mul_le_mul_of_nonneg_left hsquare hfactor0
        exact hloss.trans hrec

end

end ReachableIteration

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BohrBasic.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Elementary finite Bohr-set calculus

This file supplies the algebraic and finite-cardinality part of the Bohr-set
technology used in the proof of Erdős Problem 140.  A frequency is an additive
character with values in `ℝ / ℤ`, represented by `AddCircle 1`.  Widths are
nonnegative reals.  Keeping the frequency set separate from the width function
is useful: dilation never changes the rank, even at scale zero.

The final theorem is a general volumetric lower bound.  A finite quantization
of every circle coordinate into cells of diameter at most the corresponding
width gives

`|G| ≤ (product of the numbers of cells) * |B|`.

Thus a uniform `m`-cell quantization gives the familiar `|G| ≤ m^rank |B|`.
The theorem is stated with arbitrary quantizers so that later analytic files
can choose the most convenient short-arc partition.
-/

open scoped BigOperators

open _root_.Finset

/-- An additive character of `G`, with the target normalized as `ℝ / ℤ`. -/
abbrev AddCharacter (G : Type*) [AddCommGroup G] := G →+ AddCircle (1 : ℝ)

/-- Finite Bohr data: finitely many additive characters and one nonnegative
width for each character.  Widths away from `freq` are irrelevant. -/
structure BohrData (G : Type*) [AddCommGroup G] where
  freq : Finset (AddCharacter G)
  width : AddCharacter G → NNReal

namespace BohrData

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- The rank of a Bohr datum is the number of its frequencies. -/
def rank (B : BohrData G) : ℕ := B.freq.card

/-- Scalar dilation multiplies all widths and leaves the frequency set fixed. -/
def dilate (B : BohrData G) (t : NNReal) : BohrData G where
  freq := B.freq
  width γ := t * B.width γ

@[simp] lemma freq_dilate (B : BohrData G) (t : NNReal) :
    (B.dilate t).freq = B.freq := rfl

@[simp] lemma width_dilate (B : BohrData G) (t : NNReal) (γ : AddCharacter G) :
    (B.dilate t).width γ = t * B.width γ := rfl

@[simp] lemma rank_dilate (B : BohrData G) (t : NNReal) :
    (B.dilate t).rank = B.rank := rfl

@[simp] lemma dilate_one (B : BohrData G) : B.dilate 1 = B := by
  cases B
  simp [dilate]

@[simp] lemma dilate_dilate (B : BohrData G) (s t : NNReal) :
    (B.dilate s).dilate t = B.dilate (t * s) := by
  cases B
  simp [dilate, mul_assoc]

/-- The finite carrier of a Bohr datum. -/
noncomputable def carrier [Fintype G] (B : BohrData G) : Finset G := by
  classical
  exact Finset.univ.filter fun x ↦
    ∀ γ ∈ B.freq, ‖γ x‖ ≤ (B.width γ : ℝ)

@[simp] lemma mem_carrier [Fintype G] (B : BohrData G) (x : G) :
    x ∈ B.carrier ↔ ∀ γ ∈ B.freq, ‖γ x‖ ≤ (B.width γ : ℝ) := by
  classical
  simp [carrier]

lemma zero_mem_carrier [Fintype G] (B : BohrData G) : 0 ∈ B.carrier := by
  rw [mem_carrier]
  intro γ hγ
  simp

lemma carrier_nonempty [Fintype G] (B : BohrData G) : B.carrier.Nonempty :=
  ⟨0, B.zero_mem_carrier⟩

lemma one_le_card_carrier [Fintype G] (B : BohrData G) : 1 ≤ B.carrier.card :=
  Finset.one_le_card.mpr B.carrier_nonempty

lemma neg_mem_carrier [Fintype G] {B : BohrData G} {x : G} :
    -x ∈ B.carrier ↔ x ∈ B.carrier := by
  simp only [mem_carrier]
  constructor <;> intro hx γ hγ
  · simpa only [map_neg, norm_neg] using hx γ hγ
  · simpa only [map_neg, norm_neg] using hx γ hγ

/-- Inclusion under dilation by a larger nonnegative scalar. -/
lemma carrier_dilate_mono [Fintype G] {B : BohrData G} {s t : NNReal} (hst : s ≤ t) :
    (B.dilate s).carrier ⊆ (B.dilate t).carrier := by
  intro x hx
  rw [mem_carrier] at hx ⊢
  intro γ hγ
  have hwidth : (s : ℝ) * (B.width γ : ℝ) ≤
      (t : ℝ) * (B.width γ : ℝ) := by
    gcongr
  exact (hx γ hγ).trans hwidth

/-- The triangle inequality for two (possibly differently) dilated Bohr sets. -/
lemma add_mem_dilate [Fintype G] {B : BohrData G} {s t : NNReal} {x y : G}
    (hx : x ∈ (B.dilate s).carrier) (hy : y ∈ (B.dilate t).carrier) :
    x + y ∈ (B.dilate (s + t)).carrier := by
  rw [mem_carrier] at hx hy ⊢
  intro γ hγ
  rw [map_add]
  calc
    ‖γ x + γ y‖ ≤ ‖γ x‖ + ‖γ y‖ := norm_add_le _ _
    _ ≤ (s : ℝ) * (B.width γ : ℝ) + (t : ℝ) * (B.width γ : ℝ) :=
      add_le_add (hx γ hγ) (hy γ hγ)
    _ = ((s + t : NNReal) : ℝ) * (B.width γ : ℝ) := by
      push_cast
      ring

/-- The subtraction form of the Bohr triangle inequality. -/
lemma sub_mem_dilate [Fintype G] {B : BohrData G} {s t : NNReal} {x y : G}
    (hx : x ∈ (B.dilate s).carrier) (hy : y ∈ (B.dilate t).carrier) :
    x - y ∈ (B.dilate (s + t)).carrier := by
  rw [sub_eq_add_neg]
  exact add_mem_dilate hx (neg_mem_carrier.mpr hy)

/-- Transport Bohr data through an additive equivalence.  Frequencies are
pulled back along the inverse equivalence. -/
noncomputable def map (B : BohrData G) (e : G ≃+ H) : BohrData H := by
  classical
  exact
    { freq := B.freq.image fun γ ↦ γ.comp e.symm.toAddMonoidHom
      width := fun δ ↦ B.width (δ.comp e.toAddMonoidHom) }

@[simp] lemma width_map (B : BohrData G) (e : G ≃+ H) (δ : AddCharacter H) :
    (B.map e).width δ = B.width (δ.comp e.toAddMonoidHom) := by
  classical
  simp [map]

@[simp] lemma mem_freq_map (B : BohrData G) (e : G ≃+ H) (δ : AddCharacter H) :
    δ ∈ (B.map e).freq ↔
      ∃ γ ∈ B.freq, γ.comp e.symm.toAddMonoidHom = δ := by
  classical
  simp [map]

private lemma comp_symm_injective (e : G ≃+ H) :
    Function.Injective (fun γ : AddCharacter G ↦ γ.comp e.symm.toAddMonoidHom) := by
  intro γ δ h
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa using hx

@[simp] lemma rank_map (B : BohrData G) (e : G ≃+ H) :
    (B.map e).rank = B.rank := by
  classical
  rw [rank, rank, map]
  exact Finset.card_image_iff.mpr (comp_symm_injective e).injOn

private lemma width_map_of_mem (B : BohrData G) (e : G ≃+ H)
    (γ : AddCharacter G) :
    (B.map e).width (γ.comp e.symm.toAddMonoidHom) = B.width γ := by
  change B.width ((γ.comp e.symm.toAddMonoidHom).comp e.toAddMonoidHom) = B.width γ
  apply congrArg B.width
  ext x
  simp

/-- An equivalence maps the old carrier exactly onto the transported carrier. -/
@[simp] lemma mem_map_carrier [Fintype G] [Fintype H]
    (B : BohrData G) (e : G ≃+ H) (x : G) :
    e x ∈ (B.map e).carrier ↔ x ∈ B.carrier := by
  classical
  rw [mem_carrier, mem_carrier]
  constructor
  · intro hx γ hγ
    have hfreq : γ.comp e.symm.toAddMonoidHom ∈ (B.map e).freq := by
      exact mem_freq_map B e _ |>.mpr ⟨γ, hγ, rfl⟩
    have hh := hx (γ.comp e.symm.toAddMonoidHom) hfreq
    rw [width_map_of_mem] at hh
    have happ : (γ.comp e.symm.toAddMonoidHom) (e x) = γ x := by simp
    rwa [happ] at hh
  · intro hx δ hδ
    rcases (mem_freq_map B e δ).mp hδ with ⟨γ, hγ, rfl⟩
    rw [width_map_of_mem]
    have happ : (γ.comp e.symm.toAddMonoidHom) (e x) = γ x := by simp
    rw [happ]
    exact hx γ hγ

/-- Transport by an additive equivalence preserves Bohr cardinality. -/
@[simp] lemma card_map_carrier [Fintype G] [Fintype H]
    (B : BohrData G) (e : G ≃+ H) :
    (B.map e).carrier.card = B.carrier.card := by
  classical
  symm
  apply Finset.card_bijective e e.bijective
  intro x
  exact (mem_map_carrier B e x).symm

/-! ### The doubling automorphism of an odd cyclic group -/

/-- Multiplication by two is an additive automorphism of `ZMod N` when `N` is
odd.  It is written additively as `x ↦ x + x`, which is the form used in
three-term-progression arguments. -/
noncomputable def zmodDoublingEquiv (N : ℕ) (hN : Odd N) : ZMod N ≃+ ZMod N := by
  let f : ZMod N →+ ZMod N :=
    { toFun := fun x ↦ x + x
      map_zero' := by simp
      map_add' := by
        intro x y
        abel }
  have hunit : IsUnit (2 : ZMod N) :=
    (ZMod.isUnit_iff_coprime 2 N).2 (Nat.coprime_two_left.mpr hN)
  have hbijMul : Function.Bijective (fun x : ZMod N ↦ (2 : ZMod N) * x) :=
    IsUnit.isUnit_iff_mulLeft_bijective.mp hunit
  have hbij : Function.Bijective f := by
    simpa only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, two_mul] using hbijMul
  exact AddEquiv.ofBijective f hbij

@[simp] lemma zmodDoublingEquiv_apply (N : ℕ) (hN : Odd N) (x : ZMod N) :
    zmodDoublingEquiv N hN x = x + x := by
  simp [zmodDoublingEquiv]

@[simp] lemma rank_map_zmodDoubling (N : ℕ) (hN : Odd N) (B : BohrData (ZMod N)) :
    (B.map (zmodDoublingEquiv N hN)).rank = B.rank :=
  rank_map B (zmodDoublingEquiv N hN)

@[simp] lemma card_map_zmodDoubling (N : ℕ) [NeZero N] (hN : Odd N)
    (B : BohrData (ZMod N)) :
    (B.map (zmodDoublingEquiv N hN)).carrier.card = B.carrier.card :=
  card_map_carrier B (zmodDoublingEquiv N hN)

/-! ## A finite volumetric lower bound -/

/-- The simultaneous finite signature attached to per-frequency quantizers. -/
def signature (B : BohrData G)
    (cells : B.freq → ℕ)
    (quantize : ∀ γ : B.freq, AddCircle (1 : ℝ) → Fin (cells γ))
    (x : G) : ∀ γ : B.freq, Fin (cells γ) :=
  fun γ ↦ quantize γ (γ.1 x)

/-- A fiber of a short-cell signature injects into the Bohr carrier by subtracting
any fixed point of the fiber. -/
private lemma card_signature_fiber_le [Fintype G]
    (B : BohrData G)
    (cells : B.freq → ℕ)
    (quantize : ∀ γ : B.freq, AddCircle (1 : ℝ) → Fin (cells γ))
    (hshort : ∀ (γ : B.freq) (z w : AddCircle (1 : ℝ)),
      quantize γ z = quantize γ w → ‖z - w‖ ≤ (B.width γ.1 : ℝ))
    (a : ∀ γ : B.freq, Fin (cells γ)) :
    Fintype.card {x : G // B.signature cells quantize x = a} ≤ B.carrier.card := by
  classical
  by_cases hfiber : Nonempty {x : G // B.signature cells quantize x = a}
  · let x₀ : {x : G // B.signature cells quantize x = a} := Classical.choice hfiber
    let f : {x : G // B.signature cells quantize x = a} → {x // x ∈ B.carrier} :=
      fun x ↦ ⟨x.1 - x₀.1, by
        rw [mem_carrier]
        intro γ hγ
        have hsig : B.signature cells quantize x.1 =
            B.signature cells quantize x₀.1 := x.2.trans x₀.2.symm
        have hcoord := congrFun hsig ⟨γ, hγ⟩
        rw [map_sub]
        exact hshort ⟨γ, hγ⟩ (γ x.1) (γ x₀.1) hcoord⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hval := congr_arg Subtype.val hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card {x : G // B.signature cells quantize x = a} ≤
          Fintype.card {x // x ∈ B.carrier} := Fintype.card_le_of_injective f hf
      _ = B.carrier.card := Fintype.card_coe B.carrier
  · simp only [not_nonempty_iff] at hfiber
    simp

end BohrData

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Convolution/Discrete/Defs.lean` -/

section
/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `ddconv`: Discrete convolution of two functions
* `dddconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

## Notation

* `f ∗ᵈ g`: Convolution
* `f ○ᵈ g`: Difference convolution
* `f ∗ᵈ^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

@[expose] public section

open _root_.Finset Fintype _root_.Function
open scoped ComplexConjugate _root_.NNReal Pointwise translate

variable {G H R S : Type*} [DecidableEq G] [AddCommGroup G]

/-! ### Trivial character -/

section CommSemiring
variable [CommSemiring R]

/-- The trivial character. -/
def trivChar : G → R := fun a ↦ if a = 0 then 1 else 0

@[simp] lemma trivChar_apply (a : G) : (trivChar a : R) = if a = 0 then 1 else 0 := rfl

variable [StarRing R]

@[simp] lemma conj_trivChar : conj (trivChar : G → R) = trivChar := by ext; simp
@[simp] lemma conjneg_trivChar : conjneg (trivChar : G → R) = trivChar := by ext; simp

@[simp] lemma isSelfAdjoint_trivChar : IsSelfAdjoint (trivChar : G → R) := conj_trivChar

end CommSemiring

variable [Fintype G]

/-! ### Convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R}

/-- Convolution -/
def ddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 + x.2 = a , f x.1 * g x.2

scoped infixl:71 " ∗ᵈ " => ddconv

lemma ddconv_apply (f g : G → R) (a : G) :
    (f ∗ᵈ g) a = ∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl

@[simp] lemma ddconv_zero (f : G → R) : f ∗ᵈ 0 = 0 := by ext; simp [ddconv_apply]
@[simp] lemma zero_ddconv (f : G → R) : 0 ∗ᵈ f = 0 := by ext; simp [ddconv_apply]

lemma ddconv_add (f g h : G → R) : f ∗ᵈ (g + h) = f ∗ᵈ g + f ∗ᵈ h := by
  ext; simp [ddconv_apply, mul_add, sum_add_distrib]

lemma add_ddconv (f g h : G → R) : (f + g) ∗ᵈ h = f ∗ᵈ h + g ∗ᵈ h := by
  ext; simp [ddconv_apply, add_mul, sum_add_distrib]

lemma smul_ddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ∗ᵈ g = c • (f ∗ᵈ g) := by ext a; simp [ddconv_apply, smul_sum, smul_mul_assoc]

lemma ddconv_smul [DistribSMul H R] [SMulCommClass H R R] (c : H) (f g : G → R) :
    f ∗ᵈ c • g = c • (f ∗ᵈ g) := by ext a; simp [ddconv_apply, smul_sum, mul_smul_comm]

alias smul_ddconv_assoc := smul_ddconv
alias smul_ddconv_left_comm := ddconv_smul
@[simp] lemma translate_ddconv (a : G) (f g : G → R) : τ a f ∗ᵈ g = τ a (f ∗ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma ddconv_translate (a : G) (f g : G → R) : f ∗ᵈ τ a g = τ a (f ∗ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

lemma ddconv_comm (f g : G → R) : f ∗ᵈ g = g ∗ᵈ f :=
  funext fun a ↦ sum_equiv (Equiv.prodComm _ _) (by simp [add_comm]) <| by simp [mul_comm]

lemma mul_smul_ddconv_comm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c d : H) (f g : G → R) : (c * d) • (f ∗ᵈ g) = c • f ∗ᵈ d • g := by
  rw [smul_ddconv, ddconv_smul, mul_smul]

lemma ddconv_assoc (f g h : G → R) : f ∗ᵈ g ∗ᵈ h = f ∗ᵈ (g ∗ᵈ h) := by
  ext a
  simp only [sum_mul, mul_sum, ddconv_apply, Finset.sum_sigma']
  apply sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
    (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

lemma ddconv_left_comm (f g h : G → R) : f ∗ᵈ (g ∗ᵈ h) = g ∗ᵈ (f ∗ᵈ h) := by
  rw [← ddconv_assoc, ← ddconv_assoc, ddconv_comm g]

lemma ddconv_ddconv_ddconv_comm (f g h i : G → R) : f ∗ᵈ g ∗ᵈ (h ∗ᵈ i) = f ∗ᵈ h ∗ᵈ (g ∗ᵈ i) := by
  rw [ddconv_assoc, ddconv_assoc, ddconv_left_comm g]

lemma map_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) (a : G) :
    m ((f ∗ᵈ g) a) = (m ∘ f ∗ᵈ m ∘ g) a := by simp [ddconv_apply, map_sum, map_mul]

lemma comp_ddconv [CommSemiring S] (m : R →+* S) (f g : G → R) : m ∘ (f ∗ᵈ g) = m ∘ f ∗ᵈ m ∘ g :=
  funext <| map_ddconv _ _ _

lemma ddconv_eq_sum_sub (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f (a - t) * g t := by
  rw [ddconv_apply]; apply sum_nbij' Prod.snd (fun b ↦ (a - b, b)) <;> aesop

lemma ddconv_eq_sum_add (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f (a + t) * g (-t) :=
  (ddconv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma ddconv_eq_sum_sub' (f g : G → R) (a : G) : (f ∗ᵈ g) a = ∑ t, f t * g (a - t) := by
  rw [ddconv_comm, ddconv_eq_sum_sub]; simp_rw [mul_comm]

lemma ddconv_apply_add (f g : G → R) (a b : G) : (f ∗ᵈ g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
  (ddconv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc]

lemma sum_ddconv_mul (f g h : G → R) : ∑ a, (f ∗ᵈ g) a * h a = ∑ a, ∑ b, f a * g b * h (a + b) := by
  simp_rw [ddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma sum_ddconv (f g : G → R) : ∑ a, (f ∗ᵈ g) a = (∑ a, f a) * ∑ a, g a := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_ddconv_mul f g 1

@[simp] lemma ddconv_const (f : G → R) (b : R) : f ∗ᵈ const _ b = const _ ((∑ x, f x) * b) := by
  ext; simp [ddconv_eq_sum_sub', sum_mul]

@[simp] lemma const_ddconv (b : R) (f : G → R) : const _ b ∗ᵈ f = const _ (b * ∑ x, f x) := by
  ext; simp [ddconv_eq_sum_sub, mul_sum]

@[simp] lemma ddconv_trivChar (f : G → R) : f ∗ᵈ trivChar = f := by ext a; simp [ddconv_eq_sum_sub]
@[simp] lemma trivChar_ddconv (f : G → R) : trivChar ∗ᵈ f = f := by
  rw [ddconv_comm, ddconv_trivChar]

lemma support_ddconv_subset (f g : G → R) : support (f ∗ᵈ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_sum_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

/-! ### Difference convolution -/

variable [StarRing R]

/-- Difference convolution -/
def dddconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

scoped infixl:71 " ○ᵈ " => dddconv

lemma dddconv_apply (f g : G → R) (a : G) :
    (f ○ᵈ g) a = ∑ x : G × G with x.1 - x.2 = a , f x.1 * conj g x.2 := rfl

@[simp] lemma dddconv_zero (f : G → R) : f ○ᵈ 0 = 0 := by ext; simp [dddconv_apply]
@[simp] lemma zero_dddconv (f : G → R) : 0 ○ᵈ f = 0 := by ext; simp [dddconv_apply]
@[simp] lemma dddconv_fun_zero (f : G → R) : f ○ᵈ (fun _ ↦ 0) = 0 := by ext; simp [dddconv_apply]
@[simp] lemma fun_zero_dddconv (f : G → R) : (fun _ ↦ 0) ○ᵈ f = 0 := by ext; simp [dddconv_apply]

lemma dddconv_add (f g h : G → R) : f ○ᵈ (g + h) = f ○ᵈ g + f ○ᵈ h := by
  ext; simp [dddconv_apply, mul_add, sum_add_distrib]

lemma add_dddconv (f g h : G → R) : (f + g) ○ᵈ h = f ○ᵈ h + g ○ᵈ h := by
  ext; simp [dddconv_apply, add_mul, sum_add_distrib]

lemma smul_dddconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ○ᵈ g = c • (f ○ᵈ g) := by ext; simp [dddconv_apply, smul_sum, smul_mul_assoc]

lemma dddconv_smul [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c : H)
    (f g : G → R) : f ○ᵈ c • g = star c • (f ○ᵈ g) := by
  ext; simp [dddconv_apply, smul_sum, mul_smul_comm, starRingEnd_apply, star_smul]

@[simp] lemma translate_dddconv (a : G) (f g : G → R) : τ a f ○ᵈ g = τ a (f ○ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma dddconv_translate (a : G) (f g : G → R) : f ○ᵈ τ a g = τ (-a) (f ○ᵈ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

@[simp] lemma ddconv_conjneg (f g : G → R) : f ∗ᵈ conjneg g = f ○ᵈ g :=
  funext fun a ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.neg _) (by simp) (by simp)

@[simp] lemma dddconv_conjneg (f g : G → R) : f ○ᵈ conjneg g = f ∗ᵈ g := by
  rw [← ddconv_conjneg, conjneg_conjneg]

@[simp]
lemma conj_ddconv_apply (f g : G → R) (a : G) : conj ((f ∗ᵈ g) a) = (conj f ∗ᵈ conj g) a := by
  simp only [Pi.conj_apply, ddconv_apply, map_sum, map_mul]

@[simp]
lemma conj_dddconv_apply (f g : G → R) (a : G) : conj ((f ○ᵈ g) a) = (conj f ○ᵈ conj g) a := by
  simp_rw [← ddconv_conjneg, conj_ddconv_apply, conjneg_conj]

@[simp] lemma conj_ddconv (f g : G → R) : conj (f ∗ᵈ g) = conj f ∗ᵈ conj g :=
  funext <| conj_ddconv_apply _ _

@[simp] lemma conj_dddconv (f g : G → R) : conj (f ○ᵈ g) = conj f ○ᵈ conj g :=
  funext <| conj_dddconv_apply _ _

private lemma _root_.IsSelfAdjoint.ddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ᵈ g) :=
  (conj_ddconv _ _).trans <| congr_arg₂ _ hf hg

private lemma _root_.IsSelfAdjoint.dddconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) :
    IsSelfAdjoint (f ○ᵈ g) := (conj_dddconv _ _).trans <| congr_arg₂ _ hf hg

@[simp] lemma conjneg_ddconv (f g : G → R) : conjneg (f ∗ᵈ g) = conjneg f ∗ᵈ conjneg g := by
  funext a
  simp only [ddconv_apply, conjneg_apply, map_sum, map_mul]
  exact sum_equiv (Equiv.neg _) (by simp [← neg_eq_iff_eq_neg, add_comm]) (by simp)

@[simp] lemma conjneg_dddconv (f g : G → R) : conjneg (f ○ᵈ g) = g ○ᵈ f := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, conjneg_conjneg, ddconv_comm]
alias smul_dddconv_assoc := smul_dddconv
alias smul_dddconv_left_comm := dddconv_smul

lemma dddconv_ddconv_dddconv_comm (f g h i : G → R) : f ○ᵈ g ∗ᵈ (h ○ᵈ i) = f ∗ᵈ h ○ᵈ (g ∗ᵈ i) := by
  simp_rw [← ddconv_conjneg, conjneg_ddconv, ddconv_ddconv_ddconv_comm]

lemma dddconv_eq_sum_add (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f (a + t) * conj (g t) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_add]

lemma dddconv_eq_sum_sub' (f g : G → R) (a : G) : (f ○ᵈ g) a = ∑ t, f t * conj (g (t - a)) := by
  simp [← ddconv_conjneg, ddconv_eq_sum_sub']

lemma dddconv_apply_neg (f g : G → R) (a : G) : (f ○ᵈ g) (-a) = conj ((g ○ᵈ f) a) := by
  rw [← conjneg_dddconv f, conjneg_apply, Complex.conj_conj]

lemma dddconv_apply_sub (f g : G → R) (a b : G) :
    (f ○ᵈ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) := by
  simp [← ddconv_conjneg, sub_eq_add_neg, ddconv_apply_add, add_comm]

lemma sum_dddconv_mul (f g h : G → R) :
    ∑ a, (f ○ᵈ g) a * h a = ∑ a, ∑ b, f a * conj (g b) * h (a - b) := by
  simp_rw [dddconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact Fintype.sum_congr _ _ fun x ↦ Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma sum_dddconv (f g : G → R) : ∑ a, (f ○ᵈ g) a = (∑ a, f a) * ∑ a, conj (g a) := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_dddconv_mul f g 1

@[simp]
lemma dddconv_const (f : G → R) (b : R) : f ○ᵈ const _ b = const _ ((∑ x, f x) * conj b) := by
  ext; simp [dddconv_eq_sum_sub', sum_mul]

@[simp]
lemma const_dddconv (b : R) (f : G → R) : const _ b ○ᵈ f = const _ (b * ∑ x, conj (f x)) := by
  ext; simp [dddconv_eq_sum_add, mul_sum]

@[simp]
lemma dddconv_trivChar (f : G → R) : f ○ᵈ trivChar = f := by ext a; simp [dddconv_eq_sum_add]

@[simp] lemma trivChar_dddconv (f : G → R) : trivChar ○ᵈ f = conjneg f := by
  rw [← ddconv_conjneg, trivChar_ddconv]

end CommSemiring

section CommRing
variable [CommRing R]

@[simp] lemma ddconv_neg (f g : G → R) : f ∗ᵈ -g = -(f ∗ᵈ g) := by ext; simp [ddconv_apply]
@[simp] lemma neg_ddconv (f g : G → R) : -f ∗ᵈ g = -(f ∗ᵈ g) := by ext; simp [ddconv_apply]

lemma ddconv_sub (f g h : G → R) : f ∗ᵈ (g - h) = f ∗ᵈ g - f ∗ᵈ h := by
  simp only [sub_eq_add_neg, ddconv_add, ddconv_neg]

lemma sub_ddconv (f g h : G → R) : (f - g) ∗ᵈ h = f ∗ᵈ h - g ∗ᵈ h := by
  simp only [sub_eq_add_neg, add_ddconv, neg_ddconv]

variable [StarRing R]

@[simp] lemma dddconv_neg (f g : G → R) : f ○ᵈ -g = -(f ○ᵈ g) := by ext; simp [dddconv_apply]
@[simp] lemma neg_dddconv (f g : G → R) : -f ○ᵈ g = -(f ○ᵈ g) := by ext; simp [dddconv_apply]

lemma dddconv_sub (f g h : G → R) : f ○ᵈ (g - h) = f ○ᵈ g - f ○ᵈ h := by
  simp only [sub_eq_add_neg, dddconv_add, dddconv_neg]

lemma sub_dddconv (f g h : G → R) : (f - g) ○ᵈ h = f ○ᵈ h - g ○ᵈ h := by
  simp only [sub_eq_add_neg, add_dddconv, neg_dddconv]

end CommRing

section
open _root_.RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

@[simp, norm_cast]
private lemma _root_.RCLike.coe_ddconv : (↑((f ∗ᵈ g) a) : 𝕜) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a :=
  map_ddconv (algebraMap ℝ 𝕜) _ _ _

@[simp, norm_cast]
private lemma _root_.RCLike.coe_dddconv : (↑((f ○ᵈ g) a) : 𝕜) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := by simp [dddconv_apply]

@[simp]
private lemma _root_.RCLike.coe_comp_ddconv : ((↑) : ℝ → 𝕜) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g := funext <| coe_ddconv _ _

@[simp]
private lemma _root_.RCLike.coe_comp_dddconv : ((↑) : ℝ → 𝕜) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g := funext <| coe_dddconv _ _

end

section
open _root_.Complex
variable (f g : G → ℝ) (n : ℕ) (a : G)

@[simp, norm_cast]
private lemma _root_.Complex.ofReal_ddconv : (↑((f ∗ᵈ g) a) : ℂ) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a := RCLike.coe_ddconv _ _ _

@[simp, norm_cast]
private lemma _root_.Complex.ofReal_dddconv : (↑((f ○ᵈ g) a) : ℂ) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := RCLike.coe_dddconv _ _ _

@[simp] private lemma _root_.Complex.ofReal_comp_ddconv : ((↑) : ℝ → ℂ) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g :=
  funext <| ofReal_ddconv _ _

@[simp] private lemma _root_.Complex.ofReal_comp_dddconv : ((↑) : ℝ → ℂ) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g :=
  funext <| ofReal_dddconv _ _

end

section
open _root_.NNReal
variable (f g : G → ℝ≥0) (a : G)

@[simp, norm_cast]
private lemma _root_.NNReal.coe_ddconv : (↑((f ∗ᵈ g) a) : ℝ) = ((↑) ∘ f ∗ᵈ (↑) ∘ g) a := map_ddconv NNReal.toRealHom _ _ _

@[simp, norm_cast]
private lemma _root_.NNReal.coe_dddconv : (↑((f ○ᵈ g) a) : ℝ) = ((↑) ∘ f ○ᵈ (↑) ∘ g) a := by simp [dddconv_apply, coe_sum]

@[simp] private lemma _root_.NNReal.coe_comp_ddconv : ((↑) : _ → ℝ) ∘ (f ∗ᵈ g) = (↑) ∘ f ∗ᵈ (↑) ∘ g :=
  funext <| coe_ddconv _ _

@[simp] private lemma _root_.NNReal.coe_comp_dddconv : ((↑) : _ → ℝ) ∘ (f ○ᵈ g) = (↑) ∘ f ○ᵈ (↑) ∘ g :=
  funext <| coe_dddconv _ _

end

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

/-- Iterated convolution. -/
def iterConv (f : G → R) : ℕ → G → R
  | 0 => trivChar
  | n + 1 => iterConv f n ∗ᵈ f

scoped infixl:78 " ∗ᵈ^ " => iterConv

@[simp] lemma iterConv_zero (f : G → R) : f ∗ᵈ^ 0 = trivChar := rfl
@[simp] lemma iterConv_one (f : G → R) : f ∗ᵈ^ 1 = f := trivChar_ddconv _

lemma iterConv_succ (f : G → R) (n : ℕ) : f ∗ᵈ^ (n + 1) = f ∗ᵈ^ n ∗ᵈ f := rfl
lemma iterConv_succ' (f : G → R) (n : ℕ) : f ∗ᵈ^ (n + 1) = f ∗ᵈ f ∗ᵈ^ n := ddconv_comm _ _

@[simp] lemma zero_iterConv : ∀ {n}, n ≠ 0 → (0 : G → R) ∗ᵈ^ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => ddconv_zero _

@[simp] lemma smul_iterConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c : H) (f : G → R) : ∀ n, (c • f) ∗ᵈ^ n = c ^ n • f ∗ᵈ^ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterConv_succ, smul_iterConv _ _ n, pow_succ, mul_smul_ddconv_comm]

lemma comp_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (f ∗ᵈ^ n) = m ∘ f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, comp_ddconv, comp_iterConv]

lemma map_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) (a : G) (n : ℕ) :
    m ((f ∗ᵈ^ n) a) = (m ∘ f ∗ᵈ^ n) a := congr_fun (comp_iterConv m _ _) _

@[simp] lemma iterConv_trivChar : ∀ n, (trivChar : G → R) ∗ᵈ^ n = trivChar
  | 0 => rfl
  | _n + 1 => (ddconv_trivChar _).trans <| iterConv_trivChar _

variable [StarRing R]

@[simp] lemma conj_iterConv (f : G → R) : ∀ n, conj (f ∗ᵈ^ n) = conj f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conj_iterConv]

@[simp] lemma conj_iterConv_apply (f : G → R) (n : ℕ) (a : G) :
    conj ((f ∗ᵈ^ n) a) = (conj f ∗ᵈ^ n) a := congr_fun (conj_iterConv _ _) _

private lemma _root_.IsSelfAdjoint.iterConv (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (f ∗ᵈ^ n) :=
  (conj_iterConv _ _).trans <| congr_arg (· ∗ᵈ^ n) hf

@[simp]
lemma conjneg_iterConv (f : G → R) : ∀ n, conjneg (f ∗ᵈ^ n) = conjneg f ∗ᵈ^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conjneg_iterConv]

end CommSemiring

section
open _root_.NNReal

@[simp, norm_cast]
private lemma _root_.NNReal.ofReal_iterConv (f : G → ℝ≥0) (n : ℕ) (a : G) : (↑((f ∗ᵈ^ n) a) : ℝ) = ((↑) ∘ f ∗ᵈ^ n) a :=
  map_iterConv NNReal.toRealHom _ _ _

end

section
open _root_.Complex

@[simp, norm_cast]
private lemma _root_.Complex.ofReal_iterConv (f : G → ℝ) (n : ℕ) (a : G) : (↑((f ∗ᵈ^ n) a) : ℂ) = ((↑) ∘ f ∗ᵈ^ n) a :=
  map_iterConv ofRealHom _ _ _

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Analysis/RCLike/Basic.lean` -/

section
section
open _root_.RCLike
variable {K : Type*} [RCLike K]

@[simp] private lemma _root_.RCLike.enorm_ofReal (r : ℝ) : ‖(r : K)‖ₑ = ‖r‖ₑ := by simp [enorm]

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/LpNorm/Discrete/Defs.lean` -/

section
/-!
# Lp norms
-/

@[expose] public section

open _root_.Finset _root_.Function _root_.Real
open scoped BigOperators ComplexConjugate _root_.ENNReal _root_.NNReal NNRat

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {α 𝕜 R E : Type*} [MeasurableSpace α]

section
open _root_.MeasureTheory
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}

/-- The Lp norm of a function with the compact normalisation. -/
private noncomputable def _root_.MeasureTheory.dLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ := lpNorm f p .count

scoped notation "‖" f "‖_[" p "]" => dLpNorm p f

@[simp] private lemma _root_.MeasureTheory.dLpNorm_nonneg : 0 ≤ ‖f‖_[p] := by simp [dLpNorm]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_exponent_zero (f : α → E) : ‖f‖_[0] = 0 := by simp [dLpNorm]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_zero (p : ℝ≥0∞) : ‖(0 : α → E)‖_[p] = 0 := by simp [dLpNorm]
@[simp] private lemma _root_.MeasureTheory.dLpNorm_zero' (p : ℝ≥0∞) : ‖(fun _ ↦ 0 : α → E)‖_[p] = 0 := by simp [dLpNorm]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : ‖f‖_[p] = 0 := by
  simp [dLpNorm]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_neg (f : α → E) (p : ℝ≥0∞) : ‖-f‖_[p] = ‖f‖_[p] := by simp [dLpNorm]
@[simp] private lemma _root_.MeasureTheory.dLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : ‖fun x ↦ -f x‖_[p] = ‖f‖_[p] := by
  simp [dLpNorm]

private lemma _root_.MeasureTheory.dLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) : ‖f - g‖_[p] = ‖g - f‖_[p] := by
  simp [dLpNorm, lpNorm_sub_comm]

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_norm (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖fun i ↦ ‖f i‖‖_[p] = ‖f‖_[p] :=
  lpNorm_norm hf.aestronglyMeasurable _

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖|f|‖_[p] = ‖f‖_[p] :=
  lpNorm_abs hf.aestronglyMeasurable _

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_fun_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    ‖fun i ↦ |f i|‖_[p] = ‖f‖_[p] :=
  lpNorm_fun_abs hf.aestronglyMeasurable _

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

private lemma _root_.MeasureTheory.dLpNorm_const_smul [Module 𝕜 E] [NormSMulClass 𝕜 E] (c : 𝕜) (f : α → E) :
    ‖c • f‖_[p] = ‖c‖ * ‖f‖_[p] := by simp [dLpNorm, lpNorm_const_smul]

private lemma _root_.MeasureTheory.dLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) :
    ‖n • f‖_[p] = n • ‖f‖_[p] := by simp [dLpNorm, lpNorm_nsmul]

variable [NormedSpace ℝ 𝕜]

end NormedField

section RCLike
variable {p : ℝ≥0∞}

@[simp] private lemma _root_.MeasureTheory.dLpNorm_conj [RCLike R] (f : α → R) : ‖conj f‖_[p] = ‖f‖_[p] := lpNorm_conj ..

end RCLike

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]

private lemma _root_.MeasureTheory.dLpNorm_add_le (hp : 1 ≤ p) : ‖f + g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  lpNorm_add_le .of_discrete hp

private lemma _root_.MeasureTheory.dLpNorm_sub_le (hp : 1 ≤ p) : ‖f - g‖_[p] ≤ ‖f‖_[p] + ‖g‖_[p] :=
  lpNorm_sub_le .of_discrete hp

private lemma _root_.MeasureTheory.dLpNorm_expect_le [Module ℚ≥0 E] [NormedSpace ℝ E] {ι : Type*} {s : Finset ι} {f : ι → α → E}
    (hp : 1 ≤ p) : ‖𝔼 i ∈ s, f i‖_[p] ≤ 𝔼 i ∈ s, ‖f i‖_[p] :=
  lpNorm_expect_le (fun _ _ ↦ .of_discrete) hp

private lemma _root_.MeasureTheory.dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (hp : 1 ≤ p) :
    ‖f - h‖_[p] ≤ ‖f - g‖_[p] + ‖g - h‖_[p] :=
  lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub .of_discrete .of_discrete hp

end DiscreteMeasurableSpace

variable [Fintype α]

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_const' {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) (a : E) :
    ‖fun _i : α ↦ a‖_[p] = ‖a‖₊ * Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by
  simp [dLpNorm, Measure.real, *]

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

@[simp] private lemma _root_.MeasureTheory.dLpNorm_one [Nonempty α] (hp : p ≠ 0) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_one' (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    ‖(1 : α → 𝕜)‖_[p] = Fintype.card α ^ (p.toReal⁻¹ : ℝ) := by simp [dLpNorm, Measure.real, *]

end NormedField

variable [DiscreteMeasurableSpace α]

private lemma _root_.MeasureTheory.dLpNorm_eq_sum_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [dLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, integral_fintype]

private lemma _root_.MeasureTheory.dLpNorm_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] = (∑ i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  dLpNorm_eq_sum_norm' (by simpa using hp) (by simp) _

private lemma _root_.MeasureTheory.dLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖_[p] ^ (p : ℝ) = ∑ i, ‖f i‖ ^ (p : ℝ) := by
  rw [dLpNorm_eq_sum_norm hp, Real.rpow_inv_rpow (by positivity) (mod_cast hp)]

private lemma _root_.MeasureTheory.dLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) : ‖f‖_[p] ^ p = ∑ i, ‖f i‖ ^ p := by
  simpa using dLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) f

private lemma _root_.MeasureTheory.dL2Norm_sq_eq_sum_norm (f : α → E) : ‖f‖_[2] ^ 2 = ∑ i, ‖f i‖ ^ 2 := by
  simpa using dLpNorm_pow_eq_sum_norm two_ne_zero _

private lemma _root_.MeasureTheory.dL1Norm_eq_sum_norm (f : α → E) : ‖f‖_[1] = ∑ i, ‖f i‖ := by simp [dLpNorm_eq_sum_norm']

omit [Fintype α]
variable [Finite α]

private lemma _root_.MeasureTheory.dLinftyNorm_eq_iSup_norm (f : α → E) : ‖f‖_[∞] = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α <;> simp [dLpNorm, lpNorm_exponent_top_eq_essSup]

private lemma _root_.MeasureTheory.norm_le_dLinftyNorm {i : α} : ‖f i‖ ≤ ‖f‖_[∞] := by
  rw [dLinftyNorm_eq_iSup_norm]; exact le_ciSup (f := fun i ↦ ‖f i‖) (Finite.bddAbove_range _) i

@[simp] private lemma _root_.MeasureTheory.dLpNorm_eq_zero (hp : p ≠ 0) : ‖f‖_[p] = 0 ↔ f = 0 := by
  simp [dLpNorm, lpNorm_eq_zero .of_discrete hp, ae_eq_top.2]

@[simp] private lemma _root_.MeasureTheory.dLpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖_[p] ↔ f ≠ 0 :=
  lpNorm_nonneg.lt_iff_ne'.trans (dLpNorm_eq_zero hp).not

omit [Finite α]
variable [Fintype α]

end

section
open Mathlib.Meta.Positivity
open Lean Meta Qq _root_.Function _root_.MeasureTheory

alias ⟨_, dLpNorm_pos_of_ne_zero⟩ := dLpNorm_pos

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity ‖_‖_[_]] meta def evalDLpNorm : _root_.Mathlib.Meta.Positivity.PositivityExt where eval {u} R _z _p e :=
  match _p with
  | none => pure .none
  | some _ => do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@dLpNorm $α $E $instαmeas $instEnorm $p $f) =>
    assumeInstancesCommute
    try {
      let some pp := (← core q(inferInstance) (some q(inferInstance)) p).toNonzero | failure
      try
        let _pE ← synthInstanceQ q(PartialOrder $E)
        let _ ← synthInstanceQ q(Finite $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        let some pf := (← core q(inferInstance) (some q(inferInstance)) f).toNonzero | failure
        return .positive q(@dLpNorm_pos_of_ne_zero $α _ _ _ _ _ _ _ $pp $pf)
      catch _ =>
        assumeInstancesCommute
        let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
        let pf : Q($f ≠ 0) := .fvar pf
        let _ ← synthInstanceQ q(Fintype $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        return .positive q(dLpNorm_pos_of_ne_zero $pp $pf)
    } catch _ =>
      return .nonnegative q(dLpNorm_nonneg)
  | _ => throwError "not dLpNorm"

section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}

end NormedAddCommGroup

section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {f : α → ℂ}

end Complex
end Examples
end

/-! ### Hölder inequality -/

section
open _root_.MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

end Hoelder

section
variable {α : Type*} {mα : MeasurableSpace α}

@[simp]
private lemma _root_.MeasureTheory.RCLike.dLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) : ‖((↑) : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [dLpNorm, lpNorm, comp_def]
  rw! (castMode := .all)
    [RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
  simp [eLpNorm, eLpNorm', eLpNormEssSup]

@[simp] private lemma _root_.MeasureTheory.Complex.dLpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖_[p] = ‖f‖_[p] :=
  RCLike.dLpNorm_coe_comp ..

end
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/LpNorm/Weighted.lean` -/

section
/-!
# Lp norms
-/

open _root_.Finset _root_.Function _root_.Real _root_.MeasureTheory
open scoped ComplexConjugate _root_.ENNReal _root_.NNReal translate

variable {α 𝕜 E : Type*} [MeasurableSpace α]

/-! #### Weighted Lp norm -/

section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {w : α → ℝ≥0} {f g h : α → E}

/-- The weighted Lp norm of a function. -/
noncomputable def wLpNorm (p : ℝ≥0∞) (w : α → ℝ≥0) (f : α → E) : ℝ :=
  lpNorm f p <| .sum fun i ↦ w i • .dirac i

scoped notation "‖" f "‖_[" p ", " w "]" => wLpNorm p w f

@[simp] lemma wLpNorm_nonneg : 0 ≤ ‖f‖_[p, w] := by simp [wLpNorm]

@[simp] lemma wLpNorm_zero (w : α → ℝ≥0) : ‖(0 : α → E)‖_[p, w] = 0 := by simp [wLpNorm]

@[simp] lemma wLpNorm_neg (w : α → ℝ≥0) (f : α → E) : ‖-f‖_[p, w] = ‖f‖_[p, w] := by
  simp [wLpNorm]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma wLpNorm_one_eq_dLpNorm (p : ℝ≥0∞) (f : α → E) : ‖f‖_[p, 1] = ‖f‖_[p] := by
  simp only [wLpNorm, lpNorm, Pi.one_apply, one_smul, dLpNorm, Measure.count]
  congr!
  simp

@[simp] lemma wLpNorm_fun_one_eq_dLpNorm (p : ℝ≥0∞) (f : α → E) : ‖f‖_[p, fun _ ↦ 1] = ‖f‖_[p] :=
  wLpNorm_one_eq_dLpNorm ..

@[simp] lemma wLpNorm_exponent_zero (w : α → ℝ≥0) (f : α → E) : ‖f‖_[0, w] = 0 := by simp [wLpNorm]

@[simp]
lemma wLpNorm_norm (w : α → ℝ≥0) (hf : StronglyMeasurable f) :
    ‖fun i ↦ ‖f i‖‖_[p, w] = ‖f‖_[p, w] := lpNorm_norm hf.aestronglyMeasurable _

lemma wLpNorm_smul [NormedField 𝕜] [NormedSpace 𝕜 E] (c : 𝕜) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    ‖c • f‖_[p, w] = ‖c‖₊ * ‖f‖_[p, w] := lpNorm_const_smul ..

lemma wLpNorm_nsmul [NormedSpace ℝ E] (n : ℕ) (f : α → E) (p : ℝ≥0∞) (w : α → ℝ≥0) :
    ‖n • f‖_[p, w] = n • ‖f‖_[p, w] := lpNorm_nsmul ..

section RCLike
variable {K : Type*} [RCLike K]

@[simp] lemma wLpNorm_conj (f : α → K) : ‖conj f‖_[p, w] = ‖f‖_[p, w] := lpNorm_conj ..

end RCLike

variable [Finite α]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma wLpNorm_const_right (hp : p ≠ ∞) (w : ℝ≥0) (f : α → E) :
    ‖f‖_[p, const _ w] = w ^ p.toReal⁻¹ * ‖f‖_[p] := by
  cases nonempty_fintype α
  simp [wLpNorm, dLpNorm, ← Finset.smul_sum, lpNorm_smul_measure_of_ne_top hp, Measure.count,
    NNReal.smul_def]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma wLpNorm_smul_right (hp : p ≠ ⊤) (c : ℝ≥0) (f : α → E) :
    ‖f‖_[p, c • w] = c ^ p.toReal⁻¹ * ‖f‖_[p, w] := by
  cases nonempty_fintype α
  simp [wLpNorm, mul_smul, ← Finset.smul_sum, lpNorm_smul_measure_of_ne_top hp, NNReal.smul_def]

variable [Fintype α] [DiscreteMeasurableSpace α]

lemma wLpNorm_eq_sum_norm (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] = (∑ i, w i • ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [wLpNorm, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete, NNReal.smul_def,
    integral_finsetSum_measure]

lemma wLpNorm_rpow_eq_sum_norm {p : ℝ≥0} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ (p : ℝ) = ∑ i, w i • ‖f i‖ ^ (p : ℝ) := by
  rw [wLpNorm_eq_sum_norm (mod_cast hp) (by simp), ENNReal.coe_toReal,
    Real.rpow_inv_rpow _ (mod_cast hp)]
  simp only [NNReal.smul_def, smul_eq_mul]
  positivity

lemma wLpNorm_pow_eq_sum_norm {p : ℕ} (hp : p ≠ 0) (w : α → ℝ≥0) (f : α → E) :
    ‖f‖_[p, w] ^ p = ∑ i, w i • ‖f i‖ ^ p := by
  simpa using wLpNorm_rpow_eq_sum_norm (Nat.cast_ne_zero.2 hp) w f

/-- Monotonicity of weighted `L^p` norms in the exponent, for probability weights. -/
@[gcongr]
lemma wLpNorm_mono_right
    (hw : ∑ i, (w i : ℝ≥0∞) = 1) (hpq : p ≤ q) (f : α → E) :
    ‖f‖_[p, w] ≤ ‖f‖_[q, w] := by
  have : IsProbabilityMeasure (Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac (i : α)) := by
    rw [isProbabilityMeasure_iff, Measure.sum_apply _ MeasurableSet.univ]
    simp [hw, ← Measure.coe_nnreal_smul]
  rw [wLpNorm, wLpNorm,
      ← toReal_eLpNorm (μ := Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac i)
        (MemLp.of_discrete (p := p)).aestronglyMeasurable,
      ← toReal_eLpNorm (μ := Measure.sum fun i ↦ (w i : ℝ≥0) • Measure.dirac i)
        (MemLp.of_discrete (p := q)).aestronglyMeasurable]
  exact ENNReal.toReal_mono (MemLp.of_discrete (p := q)).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq (MemLp.of_discrete (p := p)).aestronglyMeasurable)

omit [Fintype α]

section one_le

lemma wLpNorm_add_le (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f + g‖_[p, w] ≤ ‖f‖_[p, w] + ‖g‖_[p, w] := lpNorm_add_le .of_discrete hp

lemma wLpNorm_le_add_wLpNorm_add (hp : 1 ≤ p) (w : α → ℝ≥0) (f g : α → E) :
    ‖f‖_[p, w] ≤ ‖f + g‖_[p, w] + ‖g‖_[p, w] := by simpa using wLpNorm_add_le hp w (f + g) (-g)

end one_le

end NormedAddCommGroup

section Real
variable [DiscreteMeasurableSpace α] {p : ℝ≥0∞} {w : α → ℝ≥0} {f g : α → ℝ}

@[simp]
lemma wLpNorm_one [Fintype α] (hp₀ : p ≠ 0) (hp : p ≠ ∞) (w : α → ℝ≥0) :
    ‖(1 : α → ℝ)‖_[p, w] = (∑ i, w i) ^ p.toReal⁻¹ := by
  simp [wLpNorm_eq_sum_norm hp₀ hp, NNReal.smul_def]

end Real

section wLpNorm
variable [Finite α] [DiscreteMeasurableSpace α] {p : ℝ≥0} {w : α → ℝ≥0}

variable [AddCommGroup α]

@[simp] lemma wLpNorm_translate [NormedAddCommGroup E] (a : α) (f : α → E) :
    ‖τ a f‖_[p, τ a w] = ‖f‖_[p, w] := by
  cases nonempty_fintype α
  obtain rfl | hp := eq_or_ne p 0 <;>
    simp [wLpNorm_eq_sum_norm, *, NNReal.smul_def, ← sum_translate a fun x ↦ w x * ‖f x‖ ^ (_ : ℝ)]

end wLpNorm

section
open Mathlib.Meta.Positivity
open Lean Meta Qq _root_.Function _root_.MeasureTheory

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p, w]`. -/
@[positivity ‖_‖_[_, _]] meta def evalWLpNorm : _root_.Mathlib.Meta.Positivity.PositivityExt where eval {u} R _z _p e :=
  match _p with
  | none => pure .none
  | some _ => do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@wLpNorm $α $E $instαmeas $instEnorm $p $w $f) =>
    assumeInstancesCommute
    return .nonnegative q(wLpNorm_nonneg)
  | _ => throwError "not wLpNorm"

end

end

/-! ### Upstream module `/tmp/addcombi/AddCombi/Mathlib/Algebra/Notation/Indicator.lean` -/

section
scoped[Indicator] notation3 "𝟭_[" s ", " R "]" => Set.indicator s fun _ ↦ (1 : R)

open scoped Indicator

scoped[Indicator] notation3 "𝟭_[" s "]" => 𝟭_[s, _]

end

/-! ### Upstream module `/tmp/addcombi/AddCombi/Mathlib/Algebra/GroupWithZero/Indicator.lean` -/

section
open scoped Indicator

variable {F α β M₀ N₀ : Type*}

section
open _root_.Set
variable [MonoidWithZero M₀] [MonoidWithZero N₀] {s : Set α}

private lemma _root_.Set.indicator_one_inter_apply (s t : Set α) (x : α) : 𝟭_[s ∩ t, M₀] x = 𝟭_[s] x * 𝟭_[t] x := by
  classical simp [indicator_apply, ← ite_and, and_comm]

private lemma _root_.Set.map_indicator_one [FunLike F M₀ N₀] [MonoidWithZeroHomClass F M₀ N₀] (f : F) (s : Set α)
    (x : α) : f (𝟭_[s] x) = 𝟭_[s] x := by classical exact MonoidWithZeroHom.map_ite_one_zero ..

variable (M₀) in
@[simp] private lemma _root_.Set.indicator_one_image (e : α ≃ β) (s : Set α) (b : β) :
    𝟭_[e '' s, M₀] b = 𝟭_[s] (e.symm b) := by classical simp [indicator_apply, ← e.eq_symm_apply]

variable [Nontrivial M₀] {a : α}

@[simp high] private lemma _root_.Set.indicator_one_apply_eq_zero : 𝟭_[s, M₀] a = 0 ↔ a ∉ s := by
  classical exact one_ne_zero.ite_eq_right_iff

private lemma _root_.Set.indicator_one_apply_ne_zero : 𝟭_[s, M₀] a ≠ 0 ↔ a ∈ s := by
  classical exact one_ne_zero.ite_ne_right_iff

@[simp high] private lemma _root_.Set.indicator_one_eq_zero : 𝟭_[s, M₀] = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]

variable (M₀) in
@[simp high] private lemma _root_.Set.support_indicator_one : 𝟭_[s, M₀].support = s := by
  ext; exact indicator_one_apply_ne_zero

end

end

/-! ### Upstream module `/tmp/addcombi/AddCombi/Mathlib/Algebra/Star/Pi.lean` -/

section
open scoped ComplexConjugate Indicator

section
open _root_.Set
variable {α R : Type*} [CommSemiring R] [StarRing R]

@[simp] private lemma _root_.Set.conj_indicator_one_apply (s : Set α) (a : α) : conj (𝟭_[s, R] a) = 𝟭_[s] a := by
  classical simp [indicator_apply]

@[simp] private lemma _root_.Set.conj_indicator_one (s : Set α) : conj 𝟭_[s, R] = 𝟭_[s] := by ext; simp

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean` -/

section
open scoped Pointwise Indicator

variable {G M₀ : Type*}

section OneZero
variable [One M₀] [Zero M₀] [Group G]

@[to_additive (dont_translate := M₀) (attr := simp) indicator_one_neg]
lemma indicator_one_inv (s : Set G) (a : G) : 𝟭_[s⁻¹, M₀] a = 𝟭_[s] a⁻¹ := by
  classical simp [Set.indicator_apply]

end OneZero

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Mu.lean` -/

section
/-!
# Normalised indicator
-/

open _root_.Finset _root_.Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise translate Indicator

variable {K L α G : Type*}

section DivisionSemiring
variable [DivisionSemiring K] [DivisionSemiring L] {s : Finset α}

/-- The normalised indicator_one of a set. -/
@[expose] noncomputable def mu (s : Finset α) : α → K := (#s : K)⁻¹ • 𝟭_[s]

scoped notation "μ " => mu
scoped notation "μ_[" K "] " => @mu K _ _

lemma mu_apply [DecidableEq α] (x : α) : μ s x = (#s : K)⁻¹ * ite (x ∈ s) 1 0 := by
  simp [mu, Set.indicator_apply]

@[simp] lemma mu_empty : (μ ∅ : α → K) = 0 := by ext; simp [mu]

lemma map_mu (f : K →+* L) (s : Finset α) (x : α) : f (μ s x) = μ s x := by
  simp_rw [mu, Pi.smul_apply, smul_eq_mul, map_mul, Set.map_indicator_one, map_inv₀, map_natCast]

section Nontrivial
variable [CharZero K] {a : α}

@[simp] lemma mu_apply_eq_zero : μ_[K] s a = 0 ↔ a ∉ s := by
  classical
  simp only [mu_apply, mul_boole, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
  refine imp_congr_right fun ha ↦ ?_
  simp only [ne_empty_of_mem ha]

@[simp] lemma mu_eq_zero : μ_[K] s = 0 ↔ s = ∅ := by
  simp [funext_iff, eq_empty_iff_forall_notMem]

lemma mu_ne_zero : μ_[K] s ≠ 0 ↔ s.Nonempty := mu_eq_zero.not.trans nonempty_iff_ne_empty.symm

variable (K)

@[simp] lemma support_mu (s : Finset α) : support (μ_[K] s) = s := by ext; simp

end Nontrivial

variable (K)

lemma card_smul_mu [CharZero K] (s : Finset α) : #s • μ_[K] s = 𝟭_[s] := by
  classical
  ext x : 1
  simp only [Pi.smul_apply, mu_apply, mul_ite, mul_one, mul_zero, smul_ite, nsmul_eq_mul,
    Set.indicator_apply, SetLike.mem_coe]
  split_ifs with h
  · have : s.Nonempty := ⟨_, h⟩
    simp [this.ne_empty]
  · simp

lemma card_smul_mu_apply [CharZero K] (s : Finset α) (x : α) : #s • μ_[K] s x = 𝟭_[s] x :=
  congr_fun (card_smul_mu K _) _

@[simp] lemma sum_mu [CharZero K] [Fintype α] (hs : s.Nonempty) : ∑ x, μ_[K] s x = 1 := by
  classical
  simpa [mu_apply] using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hs.card_pos.ne')

section Group
variable [Group G] [MulAction G α] [DecidableEq α]

@[to_additive (dont_translate := K) (attr := simp)]
lemma mu_smul (g : G) (s : Finset α) (a : α) : μ_[K] (g • s) a = μ s (g⁻¹ • a) := by
  simp [mu_apply, inv_smul_mem_iff]

end Group

section Group
variable [Group α] [DecidableEq α]

@[to_additive (dont_translate := K) (attr := simp)]
lemma mu_inv (s : Finset α) (a : α) : μ_[K] s⁻¹ a = μ s a⁻¹ := by simp [mu]

end Group

lemma translate_mu [AddCommGroup G] [DecidableEq G] (a : G) (s : Finset G) :
    τ a (μ_[K] s) = μ (a +ᵥ s) := by
  ext; simp [mu_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

end DivisionSemiring

section Semifield
variable (K) [Semifield K] {s : Finset G}

variable [StarRing K]

@[simp] lemma conjneg_mu [AddCommGroup G] [DecidableEq G] (s : Finset G) :
    conjneg (μ_[K] s) = μ (-s) := by ext; simp [mu_apply]; split_ifs <;> simp

end Semifield

section Semifield
variable (K) [Semifield K] [StarRing K] {s : Finset α}

@[simp] lemma conj_mu_apply (s : Finset α) (a : α) : conj (μ_[K] s a) = μ s a := by simp [mu]

@[simp] lemma conj_mu (s : Finset α) : conj (μ_[K] s) = μ s := by ext; simp

end Semifield

section LinearOrderedSemifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset α}

@[simp] lemma mu_nonneg : 0 ≤ μ_[K] s := fun a ↦ by classical rw [mu_apply]; split_ifs <;> simp
@[simp] lemma mu_pos : 0 < μ_[K] s ↔ s.Nonempty := mu_nonneg.lt_iff_ne'.trans mu_ne_zero

protected alias ⟨_, Finset.Nonempty.mu_pos⟩ := mu_pos

end LinearOrderedSemifield

section
open _root_.Complex
variable (s : Finset α) (a : α)

@[simp, norm_cast] private lemma _root_.Complex.ofReal_mu : ↑(μ_[ℝ] s a) = μ_[ℂ] s a := map_mu (algebraMap ℝ ℂ) ..
@[simp] private lemma _root_.Complex.ofReal_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[ℂ] s := funext <| ofReal_mu _

end

section
open _root_.RCLike
variable {𝕜 : Type*} [RCLike 𝕜] (s : Finset α) (a : α)

@[simp, norm_cast] private lemma _root_.RCLike.coe_mu : ↑(μ_[ℝ] s a) = μ_[𝕜] s a := map_mu (algebraMap ℝ 𝕜) _ _
@[simp] private lemma _root_.RCLike.coe_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[𝕜] s := funext <| coe_mu _

end

section
open _root_.NNReal
open scoped _root_.NNReal

@[simp, norm_cast]
private lemma _root_.NNReal.coe_mu (s : Finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x := map_mu NNReal.toRealHom _ _

@[simp] private lemma _root_.NNReal.coe_comp_mu (s : Finset α) : (↑) ∘ μ_[ℝ≥0] s = μ_[ℝ] s := funext <| coe_mu _

end

section
open Mathlib.Meta.Positivity
open Lean Meta Qq _root_.Function

-- private abbrev TypeFunction (α K : Type*) := α → K

-- private alias ⟨_, mu_pos_of_nonempty⟩ := mu_pos
-- #check indicator_one
-- /-- Extension for the `positivity` tactic: an indicator is nonnegative, and positive if its
-- support is nonempty. -/
-- @[positivity indicator_one _]
-- def evalindicator_one : _root_.Mathlib.Meta.Positivity.PositivityExt where eval {u π} zπ pπ e := do
--   let u1 ← mkFreshLevelMVar
--   let u2 ← mkFreshLevelMVar
--   let _ : u =QL max u1 u2 := ⟨⟩
--   match π, e with
--   | ~q(TypeFunction.{u2, u1} $α $K), ~q(@indicator_one _ _ $instα $instβ $s) =>
--     let so : Option Q(Finset.Nonempty $s) ← do -- TODO: It doesn't complain if we make a typo?
--       try
--         let _fi ← synthInstanceQ q(Fintype $α)
--         let _no ← synthInstanceQ q(Nonempty $α)
--         match s with
--         | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $α)))
--         | _ => pure none
--       catch _ => do
--         let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
--         pure (some (.fvar fv))
--     assumeInstancesCommute
--     match so with
--     | .some (fi : Q(Finset.Nonempty $s)) =>
--       try
--         let instβnontriv ← synthInstanceQ q(Nontrivial $K)
--         assumeInstancesCommute
--         return .positive q(Finset.Nonempty.indicator_one_pos $fi)
--       catch _ => return .nonnegative q(indicator_one_nonneg.{u, u_1})

--     | none => return .nonnegative q(indicator_one_nonneg.{u, u_1})
--   | _ => throwError "not Finset.indicator_one"

-- TODO: Fix

-- /-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
-- multiplicands are. -/
-- @[positivity]
-- unsafe def positivity_indicator_one : expr → tactic strictness
--   | e@q(@indicator_one $(α) $(K) $(hα) $(hβ) $(s)) ↦
--     (do
--         let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_mapp `` indicator_one_pos_of_nonempty [α, K, none, none, none, none, p])
--       do
--       nonnegative <$> mk_mapp `` indicator_one_nonneg [α, K, none, none, s]
--   | e@q(@mu $(α) $(K) $(hβ) $(hα) $(s)) ↦
--     (do
--         let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_app `` mu_pos_of_nonempty [p]) $>
--       nonnegative <$> mk_mapp `` mu_nonneg [α, K, none, none, s]
--   | e ↦ pp e >>= fail ∘ format.bracket "The expression `"
--       "` isn't of the form `𝟭_[s, K]` or `μ_[K] s`"

-- variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : Finset α}

-- example : 0 ≤ 𝟭_[s, K] := by positivity
-- example : 0 ≤ μ_[K] s := by positivity
-- example (hs : s.Nonempty) : 0 < 𝟭_[s, K] := by positivity
-- example (hs : s.Nonempty) : 0 < μ_[K] s := by positivity

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Physics/Unbalancing.lean` -/

section
/-!
# Unbalancing
-/

open _root_.Finset hiding card
open Fintype (card)
open _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped ComplexConjugate ComplexOrder _root_.NNReal _root_.ENNReal

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  {ν : G → ℝ≥0} {f : G → ℝ} {g h : G → ℂ} {ε : ℝ} {p : ℕ}

/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg' {f : G → ℂ} (hf : g ○ᵈ g = f) (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) :
    0 ≤ ⟪f ^ k, (↑) ∘ ν⟫_[ℂ] := by
  calc
    0 ≤ ∑ z : Fin k → G, (‖∑ x, (∏ i, conj (g (x + z i))) * h x‖ : ℂ) ^ 2 := by positivity
    _ = ∑ x : G, ∑ yz : G × G with yz.1 - yz.2 = x,
          h yz.1 * conj h yz.2 * conj ((g ○ᵈ g) (yz.1 - yz.2)) ^ k := ?_
    _ = ∑ x : G, ∑ yz : G × G with yz.1 - yz.2 = x,
          h yz.1 * conj h yz.2 * conj ((g ○ᵈ g) x) ^ k := by
        congr! with x _ yz hyz
        simpa using hyz
    _ = _ := by
      rw [← hf, ← hν, wInner_one_eq_sum]
      simp only [Pi.pow_apply, RCLike.inner_apply, map_pow]
      simp_rw [dddconv_apply h, sum_mul]
  simp_rw [dddconv_apply_sub, sum_fiberwise, ← univ_product_univ, sum_product]
  simp only [sum_pow', sum_mul_sum, map_mul, starRingEnd_self_apply, Fintype.piFinset_univ,
    ← Complex.conj_mul', map_sum, map_prod]
  simp only [mul_sum, @sum_comm _ _ (Fin k → G), mul_comm (conj _), prod_mul_distrib, Pi.conj_apply]
  rw [sum_comm]
  congr with x
  congr with y
  congr with z
  group

set_option backward.isDefEq.respectTransparency false in
/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
lemma pow_inner_nonneg {f : G → ℝ} (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) :
    (0 : ℝ) ≤ ⟪(↑) ∘ ν, f ^ k⟫_[ℝ] := by
  simpa [← Complex.zero_le_real, wInner_one_eq_sum, mul_comm] using pow_inner_nonneg' hf hν k

private lemma log_ε_pos (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : 0 < log (3 / ε) :=
  log_pos <| (one_lt_div hε₀).2 <| hε₁.trans_lt <| by norm_num

private lemma p'_pos (hp : 5 ≤ p) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) : 0 < 24 / ε * log (3 / ε) * p := by
  have := log_ε_pos hε₀ hε₁; positivity

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

set_option backward.isDefEq.respectTransparency false in
/-- Note that we do the physical proof in order to avoid the Fourier transform. -/
private lemma unbalancing'' (p : ℕ) (hp : 5 ≤ p) (hp₁ : Odd p) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν) (hν₁ : ∑ x, ν x = 1)
    (hε : ε ≤ ‖f‖_[p, ν]) :
    1 + ε / 2 ≤ ‖f + 1‖_[.ofReal (24 / ε * log (3 / ε) * p), ν] := by
  have hνprob : ∑ x, (ν x : ℝ≥0∞) = 1 := mod_cast hν₁
  obtain hf₁ | hf₁ := le_total 2 ‖f + 1‖_[2 * p, ν]
  · calc
      1 + ε / 2 ≤ 1 + 1 / 2 := by grw [hε₁]
      _ ≤ 2 := by norm_num
      _ ≤ ‖f + 1‖_[2 * p, ν] := hf₁
      _ ≤ _ := wLpNorm_mono_right hνprob ?_ _
    norm_cast
    rw [ENNReal.natCast_le_ofReal (by positivity)]
    push_cast
    gcongr
    calc
      2 ≤ 24 / 1 * 0.6931471803 := by norm_num
      _ ≤ 24 / ε * log (3 / ε) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hε₀ hε₁)
          (log_two_gt_d9.le.trans
            (log_le_log zero_lt_two <|
              (div_le_div_of_nonneg_left (by norm_num) hε₀ hε₁).trans' <| by norm_num))
          (by norm_num) ?_
    all_goals positivity
  have : ε ^ p ≤ 2 * ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * (f⁺) i) := by
    calc
      ε ^ p ≤ ‖f‖_[p, ν] ^ p := hp₁.strictMono_pow.monotone hε
      _ = ∑ i, ν i • ((f ^ (p - 1)) i * |f| i) := by
        rw [wLpNorm_pow_eq_sum_norm hp₁.pos.ne']
        dsimp
        refine sum_congr rfl fun i _ ↦ ?_
        rw [← abs_of_nonneg ((Nat.Odd.sub_odd hp₁ odd_one).pow_nonneg <| f _), abs_pow,
          pow_sub_one_mul hp₁.pos.ne', NNReal.smul_def, smul_eq_mul]
      _ ≤ ⟪((↑) ∘ ν : G → ℝ), f ^ p⟫_[ℝ] + ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * |f| i) :=
        (le_add_of_nonneg_left <| pow_inner_nonneg hf hν _)
      _ = ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * (f i + |f i|)) := by
        simp [wInner_one_eq_sum, mul_add, sum_add_distrib, pow_sub_one_mul hp₁.pos.ne' (f _)]
        simp [mul_comm]
      _ = ∑ i, ↑(ν i) * ((f ^ (p - 1)) i * (2 • (f i)⁺)) := by simp [add_abs_eq_two_nsmul_posPart]
      _ = _ := by simp [mul_sum, mul_left_comm (2 : ℝ)]
  set P : Finset _ := {i | 0 ≤ f i}
  set T : Finset _ := {i | 3 / 4 * ε ≤ f i}
  have hTP : T ⊆ P := by unfold P T; gcongr; positivity
  have : 2⁻¹ * ε ^ p ≤ ∑ i ∈ P, ↑(ν i) * (f ^ p) i := by
    rw [inv_mul_le_iff₀ (zero_lt_two' ℝ), sum_filter]
    convert! this using 3
    rw [Pi.posPart_apply, posPart_eq_ite]
    split_ifs <;> simp [pow_sub_one_mul hp₁.pos.ne']
  have hp' : 1 ≤ (2 * p : ℝ≥0) := by
    norm_cast
    rw [Nat.succ_le_iff]
    positivity
  have : ∑ i ∈ P \ T, ↑(ν i) * (f ^ p) i ≤ 4⁻¹ * ε ^ p := by
    calc
      _ ≤ ∑ i ∈ P \ T, ↑(ν i) * (3 / 4 * ε) ^ p := sum_le_sum fun i hi ↦ ?_
      _ = (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, (ν i : ℝ) := by rw [← sum_mul, mul_comm, mul_pow]
      _ ≤ 4⁻¹ * ε ^ p * ∑ i, (ν i : ℝ) := ?_
      _ = 4⁻¹ * ε ^ p := by norm_cast; simp_all
    · simp only [mem_sdiff, mem_filter, mem_univ, true_and, not_le, P, T] at hi
      cases hi
      dsimp
      gcongr
    · refine mul_le_mul (mul_le_mul_of_nonneg_right (le_trans (pow_le_pow_of_le_one ?_ ?_ hp) ?_)
        ?_) (sum_le_univ_sum_of_nonneg fun i ↦ ?_) ?_ ?_ <;>
        first
        | positivity
        | norm_num
  replace hf₁ : ‖f‖_[2 * p, ν] ≤ 3 := by
    calc
      _ ≤ ‖f + 1‖_[2 * p, ν] + ‖(1 : G → ℝ)‖_[2 * p, ν] :=
        wLpNorm_le_add_wLpNorm_add (mod_cast hp') _ _ _
      _ ≤ 2 + 1 := by
        gcongr
        have : 2 * (p : ℝ≥0∞) ≠ 0 := mul_ne_zero two_ne_zero (by positivity)
        simp [wLpNorm_one, ENNReal.mul_ne_top, *]
      _ = 3 := by norm_num
  replace hp' := zero_lt_one.trans_le hp'
  have : 4⁻¹ * ε ^ p ≤ Real.sqrt (∑ i ∈ T, ν i) * 3 ^ p := by
    calc
      4⁻¹ * ε ^ p = 2⁻¹ * ε ^ p - 4⁻¹ * ε ^ p := by rw [← sub_mul]; norm_num
      _ ≤ _ := (sub_le_sub ‹_› ‹_›)
      _ = ∑ i ∈ T, ν i * (f ^ p) i := by rw [sum_sdiff_eq_sub hTP, sub_sub_cancel]
      _ ≤ ∑ i ∈ T, ν i * |(f ^ p) i| :=
        (sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (le_abs_self _) ?_)
      _ = ∑ i ∈ T, Real.sqrt (ν i) * Real.sqrt (ν i * |(f ^ (2 * p)) i|) := by simp [← mul_assoc, pow_mul']
      _ ≤ Real.sqrt (∑ i ∈ T, ν i) * Real.sqrt (∑ i ∈ T, ν i * |(f ^ (2 * p)) i|) :=
        (sum_sqrt_mul_sqrt_le _ (fun i ↦ ?_) fun i ↦ ?_)
      _ ≤ Real.sqrt (∑ i ∈ T, ν i) * Real.sqrt (∑ i, ν i * |(f ^ (2 * p)) i|) := by
        gcongr; exact T.subset_univ
      _ = Real.sqrt (∑ i ∈ T, ν i) * ‖f‖_[2 * ↑p, ν] ^ p := ?_
      _ ≤ _ := by gcongr
    any_goals positivity
    rw [wLpNorm_eq_sum_norm (mod_cast hp'.ne') (by simp [ENNReal.mul_ne_top])]
    norm_cast
    rw [← rpow_mul_natCast (by positivity)]
    have : (p : ℝ) ≠ 0 := by positivity
    simp [mul_comm, this, Real.sqrt_eq_rpow, NNReal.smul_def]
  set p' := 24 / ε * log (3 / ε) * p
  have hp' : 0 < p' := p'_pos hp hε₀ hε₁
  have : 1 - 8⁻¹ * ε ≤ (∑ i ∈ T, ↑(ν i)) ^ p'⁻¹ := by
    rw [← div_le_iff₀ (by positivity), mul_div_assoc, ← div_pow,
      le_sqrt (by positivity) (by positivity), mul_pow, ← pow_mul'] at this
    calc
      _ ≤ exp (-(8⁻¹ * ε)) := one_sub_le_exp_neg _
      _ = ((ε / 3) ^ p * (ε / 3) ^ (2 * p)) ^ p'⁻¹ := ?_
      _ ≤ _ := rpow_le_rpow ?_ ((mul_le_mul_of_nonneg_right ?_ ?_).trans this) ?_
    · rw [← pow_add, ← one_add_mul _ p, ← rpow_natCast, Nat.cast_mul, ← rpow_mul, ← div_eq_mul_inv,
        mul_div_mul_right, ← exp_log (_ : 0 < ε / 3), ← exp_mul, ← inv_div, log_inv, neg_mul,
        mul_div_left_comm, div_mul_cancel_right₀ (log_ε_pos hε₀ hε₁).ne']
      any_goals positivity
      field_simp
      ring_nf
    any_goals positivity
    calc
      _ ≤ (1 / 3 : ℝ) ^ p := by gcongr
      _ ≤ (1 / 3) ^ 5 := pow_le_pow_of_le_one ?_ ?_ hp
      _ ≤ _ := ?_
    any_goals positivity
    all_goals norm_num
  calc
    1 + ε / 2 = 1 + 2⁻¹ * ε := by rw [div_eq_inv_mul]
    _ ≤ 1 + 17 / 32 * ε := by gcongr; norm_num
    _ = 1 + 5 / 8 * ε - 3 / 32 * ε * 1 := by ring
    _ ≤ 1 + 5 / 8 * ε - 3 / 32 * ε * ε := (sub_le_sub_left (mul_le_mul_of_nonneg_left hε₁ ?_) _)
    _ = (1 - 8⁻¹ * ε) * (1 + 3 / 4 * ε) := by ring
    _ ≤ (∑ i ∈ T, ↑(ν i)) ^ p'⁻¹ * (1 + 3 / 4 * ε) := (mul_le_mul_of_nonneg_right ‹_› ?_)
    _ = (∑ i ∈ T, ↑(ν i) * |3 / 4 * ε + 1| ^ p') ^ p'⁻¹ := by
      rw [← sum_mul, mul_rpow, rpow_rpow_inv, abs_of_nonneg, add_comm] <;> positivity
    _ ≤ (∑ i ∈ T, ↑(ν i) * |f i + 1| ^ p') ^ p'⁻¹ := by gcongr with i hi; exact (mem_filter.1 hi).2
    _ ≤ (∑ i, ↑(ν i) * |f i + 1| ^ p') ^ p'⁻¹ :=
        rpow_le_rpow ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ ↦ ?_) ?_
    _ = _ := by
        rw [wLpNorm_eq_sum_norm (by positivity) (by simp)]
        simp [p', (p'_pos hp hε₀ hε₁).le, NNReal.smul_def]
  all_goals positivity

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing' (p : ℕ) (hp : p ≠ 0) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (ν : G → ℝ≥0)
    (f : G → ℝ) (g h : G → ℂ) (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν)
    (hν₁ : ∑ x, ν x = 1) (hε : ε ≤ ‖f‖_[p, ν]) :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧ 1 + ε / 2 ≤ ‖f + 1‖_[p', ν] := by
  have := log_ε_pos hε₀ hε₁
  have : 5 ≤ 2 * p + 3 := by omega
  rw [← Nat.one_le_iff_ne_zero] at hp
  refine ⟨⌈120 / ε * log (3 / ε) * p⌉₊, ?_, ?_⟩
  · calc
      (⌈120 / ε * log (3 / ε) * p⌉₊ : ℝ)
        = ⌈120 * ε⁻¹ * log (3 * ε⁻¹) * p⌉₊ := by simp [div_eq_mul_inv]
      _ ≤ 2 * (120 * ε⁻¹ * log (3 * ε⁻¹) * p) := Nat.ceil_le_two_mul <|
        calc
          (2⁻¹ : ℝ) ≤ 120 * 1 * 1 * 1 := by norm_num
          _ ≤ 120 * ε⁻¹ * log (3 * ε⁻¹) * p := by
            gcongr
            · exact (one_le_inv₀ hε₀).2 hε₁
            · rw [← log_exp 1]
              gcongr
              calc
                exp 1 ≤ 2.7182818286 := exp_one_lt_d9.le
                _ ≤ 3 * 1 := by norm_num
                _ ≤ 3 * ε⁻¹ := by gcongr; exact (one_le_inv₀ hε₀).2 hε₁
            · exact mod_cast hp
      _ ≤ 2 * (120 * ε⁻¹ * (3 * ε⁻¹) * p) := by gcongr; exact Real.log_le_self (by positivity)
      _ ≤ 2 * (2 ^ 7 * ε⁻¹ * (2 ^ 2 * ε⁻¹) * p) := by gcongr <;> norm_num
      _ = 2 ^ 10 * ε⁻¹ ^ 2 * p := by ring
  have hνprob : ∑ x, (ν x : ℝ≥0∞) = 1 := mod_cast hν₁
  calc
    1 + ε / 2 ≤ ↑‖f + 1‖_[.ofReal (24 / ε * log (3 / ε) * ↑(2 * p + 3)), ν] :=
      unbalancing'' (2 * p + 3) this ((even_two_mul _).add_odd <| by decide) hε₀ hε₁ hf hν hν₁ <|
        hε.trans <| wLpNorm_mono_right hνprob
          (Nat.cast_le.2 <| le_add_of_le_left <| le_mul_of_one_le_left' one_le_two) _
    _ ≤ _ := wLpNorm_mono_right hνprob ?_ _
  norm_cast
  calc
    _ = 24 / ε * log (3 / ε) * ↑(2 * p + 3 * 1) := by simp
    _ ≤ 24 / ε * log (3 / ε) * ↑(2 * p + 3 * p) := by gcongr
    _ = 120 / ε * log (3 / ε) * p := by push_cast; ring
    _ ≤ ⌈120 / ε * log (3 / ε) * p⌉₊ := Nat.le_ceil _

/-- The unbalancing step. Note that we do the physical proof in order to avoid the Fourier
transform. -/
lemma unbalancing (p : ℕ) (hp : p ≠ 0) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (f : G → ℝ) (g h : G → ℂ)
    (hf : g ○ᵈ g = (↑) ∘ f) (hh : h ○ᵈ h = μ univ)
    (hε : ε ≤ ‖f‖_[p, μ univ]) :
    ∃ p' : ℕ, p' ≤ 2 ^ 10 * ε⁻¹ ^ 2 * p ∧ 1 + ε / 2 ≤ ‖f + 1‖_[p', μ univ] :=
  unbalancing' p hp ε hε₀ hε₁ _ _ g h hf
    (show _ = Complex.ofReal ∘ NNReal.toReal ∘ μ univ by simpa using hh) (by simp)
    (by simpa [rpow_neg, inv_rpow] using hε)

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Unbalancing.lean` -/

section
/-!
# The Kelley--Meka unbalancing lemma

This file proves the finite, power-moment form of the unbalancing step.  Keeping
the statement in power-moment form has two advantages: all exponents are
natural numbers, and no convention at exponent zero is hidden in an `L^p`
notation.  Taking the positive `p'`-th root gives the usual weighted `L^p`
form immediately.
-/

open _root_.Finset _root_.Function
open scoped BigOperators _root_.NNReal

section Moments

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The `k`-th moment of `f` with respect to the (not necessarily normalized)
weight `ν`. -/
def weightedMoment (ν f : X → ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, ν x * f x ^ k

/-- The absolute `k`-th moment. -/
def weightedAbsMoment (ν f : X → ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, ν x * |f x| ^ k

theorem weightedAbsMoment_nonneg {ν f : X → ℝ} (hν : ∀ x, 0 ≤ ν x) (k : ℕ) :
    0 ≤ weightedAbsMoment ν f k := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hν x) (pow_nonneg (abs_nonneg _) _)

/-- A convenient explicit multiplier.  The very generous constant `60` lets
Bernoulli's inequality replace the logarithm in the customary proof. -/
noncomputable def unbalancingMultiplier (ε : ℝ) : ℕ :=
  Nat.ceil (60 / ε ^ 2)

/-- The even exponent used in the small-moment branch of unbalancing. -/
noncomputable def unbalancingExponent (ε : ℝ) (p : ℕ) : ℕ :=
  2 * p * unbalancingMultiplier ε

theorem unbalancingMultiplier_pos {ε : ℝ} (hε : 0 < ε) :
    0 < unbalancingMultiplier ε := by
  rw [unbalancingMultiplier, Nat.ceil_pos]
  positivity

theorem unbalancingExponent_even (ε : ℝ) (p : ℕ) :
    Even (unbalancingExponent ε p) := by
  refine ⟨p * unbalancingMultiplier ε, ?_⟩
  simp [unbalancingExponent, two_mul, add_mul]

theorem unbalancingExponent_pos {ε : ℝ} {p : ℕ} (hε : 0 < ε) (hp : p ≠ 0) :
    0 < unbalancingExponent ε p := by
  simp [unbalancingExponent, unbalancingMultiplier_pos hε, Nat.pos_of_ne_zero hp]

theorem unbalancingMultiplier_spec {ε : ℝ} (hε : 0 < ε) :
    60 / ε ^ 2 ≤ unbalancingMultiplier ε := by
  simpa [unbalancingMultiplier] using Nat.le_ceil (60 / ε ^ 2)

private theorem add_pow_le_two_pow_mul_add_pow {a b : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 1 ≤ n) :
    (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n) := by
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a' b'
    (p := (n : ℝ)) (by exact_mod_cast hn)
  exact_mod_cast h

/-- **Unbalancing, power-moment form.**  If all moments of `f` against a
probability weight are nonnegative and the `p`-th absolute moment is at least
`ε^p`, then at some explicitly bounded even exponent the absolute moment of
`1 + f` is at least `(1 + ε/2)^p'`.

The hypotheses `Odd p` and `5 ≤ p` are the standard intermediate form.  An
arbitrary positive input exponent is replaced by `2 * p + 3` before applying
this lemma. -/
theorem unbalancing_of_nonnegative_moments
    {ν f : X → ℝ} {ε : ℝ} {p : ℕ}
    (hν : ∀ x, 0 ≤ ν x) (hνmass : ∑ x : X, ν x = 1)
    (hmom : ∀ k : ℕ, 0 ≤ weightedMoment ν f k)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hp : 5 ≤ p) (hpodd : Odd p)
    (hlarge : ε ^ p ≤ weightedAbsMoment ν f p) :
    ∃ p' : ℕ, 0 < p' ∧ Even p' ∧ p' ≤ unbalancingExponent ε p ∧
      (1 + ε / 2) ^ p' ≤ weightedAbsMoment ν (f + 1) p' := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  have hpm1even : Even (p - 1) := Nat.Odd.sub_odd hpodd odd_one
  have hpositive :
      ε ^ p ≤ 2 * ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i)⁺) := by
    calc
      ε ^ p ≤ weightedAbsMoment ν f p := hlarge
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * |f i|) := by
        unfold weightedAbsMoment
        apply sum_congr rfl
        intro i _
        congr 1
        change |f i| ^ p = f i ^ (p - 1) * |f i|
        rw [← abs_of_nonneg (hpm1even.pow_nonneg (f i)), abs_pow,
          pow_sub_one_mul hp0]
      _ ≤ weightedMoment ν f p +
          ∑ i : X, ν i * ((f ^ (p - 1)) i * |f i|) :=
        le_add_of_nonneg_left (hmom p)
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i + |f i|)) := by
        simp [weightedMoment, mul_add, sum_add_distrib, pow_sub_one_mul hp0]
      _ = ∑ i : X, ν i * ((f ^ (p - 1)) i * (2 • (f i)⁺)) := by
        simp [add_abs_eq_two_nsmul_posPart]
      _ = 2 * ∑ i : X, ν i * ((f ^ (p - 1)) i * (f i)⁺) := by
        simp [mul_sum]
        ring
  let P : Finset X := Finset.univ.filter fun i ↦ 0 ≤ f i
  let T : Finset X := Finset.univ.filter fun i ↦ 3 / 4 * ε ≤ f i
  have hTP : T ⊆ P := by
    intro i hi
    simp only [P, T, mem_filter, mem_univ, true_and] at hi ⊢
    exact le_trans (by positivity) hi
  have hP :
      (2 : ℝ)⁻¹ * ε ^ p ≤ ∑ i ∈ P, ν i * (f ^ p) i := by
    rw [inv_mul_le_iff₀ (by norm_num : (0 : ℝ) < 2), sum_filter]
    simpa [P, Pi.posPart_apply, posPart_eq_ite, pow_sub_one_mul hp0] using hpositive
  have hlow :
      ∑ i ∈ P \ T, ν i * (f ^ p) i ≤ (4 : ℝ)⁻¹ * ε ^ p := by
    calc
      _ ≤ ∑ i ∈ P \ T, ν i * (3 / 4 * ε) ^ p := by
        apply sum_le_sum
        intro i hi
        have hi' := hi
        simp only [mem_sdiff, P, T, mem_filter, mem_univ, true_and, not_le] at hi'
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hi'.1 hi'.2.le p) (hν i)
      _ = (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, ν i := by
        rw [← sum_mul]
        simp [mul_pow]
        ring
      _ ≤ (4 : ℝ)⁻¹ * ε ^ p * ∑ i : X, ν i := by
        have hpow : (3 / 4 : ℝ) ^ p ≤ (4 : ℝ)⁻¹ := by
          calc
            (3 / 4 : ℝ) ^ p ≤ (3 / 4 : ℝ) ^ 5 := by
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
            _ ≤ (4 : ℝ)⁻¹ := by norm_num
        calc
          (3 / 4) ^ p * ε ^ p * ∑ i ∈ P \ T, ν i ≤
              (4 : ℝ)⁻¹ * ε ^ p * ∑ i ∈ P \ T, ν i :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow (pow_nonneg hε₀.le p))
              (sum_nonneg fun i _ ↦ hν i)
          _ ≤ (4 : ℝ)⁻¹ * ε ^ p * ∑ i : X, ν i :=
            mul_le_mul_of_nonneg_left
              (sum_le_univ_sum_of_nonneg fun i ↦ hν i)
              (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p))
      _ = (4 : ℝ)⁻¹ * ε ^ p := by rw [hνmass, mul_one]
  have hTmoment :
      (4 : ℝ)⁻¹ * ε ^ p ≤ ∑ i ∈ T, ν i * (f ^ p) i := by
    calc
      (4 : ℝ)⁻¹ * ε ^ p =
          (2 : ℝ)⁻¹ * ε ^ p - (4 : ℝ)⁻¹ * ε ^ p := by ring
      _ ≤ (∑ i ∈ P, ν i * (f ^ p) i) -
          ∑ i ∈ P \ T, ν i * (f ^ p) i := sub_le_sub hP hlow
      _ = ∑ i ∈ T, ν i * (f ^ p) i := by
        rw [sum_sdiff_eq_sub hTP]
        ring
  have hTmoment_nonneg : 0 ≤ ∑ i ∈ T, ν i * (f ^ p) i :=
    (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p)).trans hTmoment
  have hCS :
      (∑ i ∈ T, ν i * (f ^ p) i) ^ 2 ≤
        (∑ i ∈ T, ν i) * ∑ i ∈ T, ν i * (f ^ (2 * p)) i := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul T
    · intro i _
      exact hν i
    · intro i _
      exact mul_nonneg (hν i) ((even_two_mul p).pow_nonneg (f i))
    · intro i _
      dsimp
      rw [show 2 * p = p * 2 by omega, pow_mul, mul_pow]
      ring_nf
      exact le_rfl
  have hCSabs :
      ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 ≤
        (∑ i ∈ T, ν i) * weightedAbsMoment ν f (2 * p) := by
    calc
      _ ≤ (∑ i ∈ T, ν i * (f ^ p) i) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num) (pow_nonneg hε₀.le p)) hTmoment 2
      _ ≤ (∑ i ∈ T, ν i) * ∑ i ∈ T, ν i * (f ^ (2 * p)) i := hCS
      _ ≤ (∑ i ∈ T, ν i) * weightedAbsMoment ν f (2 * p) := by
        apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun i _ ↦ hν i)
        unfold weightedAbsMoment
        have heq :
            (∑ i ∈ T, ν i * (f ^ (2 * p)) i) =
              ∑ i ∈ T, ν i * |f i| ^ (2 * p) := by
          apply sum_congr rfl
          intro i _
          simp only [Pi.pow_apply]
          rw [(even_two_mul p).pow_abs]
        rw [heq]
        apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
        intro i _ _
        exact mul_nonneg (hν i) (pow_nonneg (abs_nonneg _) _)
  let q : ℕ := 2 * p
  by_cases hbig : (2 : ℝ) ^ q ≤ weightedAbsMoment ν (f + 1) q
  · refine ⟨q, by dsimp [q]; omega, even_two_mul p, ?_, ?_⟩
    · dsimp [q, unbalancingExponent]
      exact Nat.le_mul_of_pos_right _ (unbalancingMultiplier_pos hε₀)
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) q).trans hbig
  · have hsmall : weightedAbsMoment ν (f + 1) q < (2 : ℝ) ^ q := lt_of_not_ge hbig
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hfq : weightedAbsMoment ν f q ≤ (2 : ℝ) ^ (2 * q) := by
      calc
        weightedAbsMoment ν f q ≤
            (2 : ℝ) ^ (q - 1) * (weightedAbsMoment ν (f + 1) q + 1) := by
          unfold weightedAbsMoment
          calc
            (∑ x : X, ν x * |f x| ^ q) ≤
                ∑ x : X, ν x *
                  ((2 : ℝ) ^ (q - 1) * (|f x + 1| ^ q + 1 ^ q)) := by
              apply sum_le_sum
              intro i _
              apply mul_le_mul_of_nonneg_left _ (hν i)
              calc
                |f i| ^ q ≤ (|f i + 1| + 1) ^ q := by
                  apply pow_le_pow_left₀ (abs_nonneg _) _ q
                  calc
                    |f i| = |(f i + 1) - 1| := by ring_nf
                    _ ≤ |f i + 1| + |(1 : ℝ)| := abs_sub _ _
                    _ = |f i + 1| + 1 := by norm_num
                _ ≤ (2 : ℝ) ^ (q - 1) * (|f i + 1| ^ q + 1 ^ q) :=
                  add_pow_le_two_pow_mul_add_pow (abs_nonneg _) (by norm_num) hq
            _ = (2 : ℝ) ^ (q - 1) *
                (∑ x : X, ν x * |(f + 1) x| ^ q + 1) := by
              simp only [Pi.add_apply, Pi.one_apply, one_pow]
              calc
                (∑ x : X, ν x * (2 ^ (q - 1) * (|f x + 1| ^ q + 1))) =
                    2 ^ (q - 1) * (∑ x : X, ν x * |f x + 1| ^ q) +
                      2 ^ (q - 1) * ∑ x : X, ν x := by
                  simp_rw [mul_add]
                  rw [sum_add_distrib]
                  congr 1
                  · rw [mul_sum]
                    apply sum_congr rfl
                    intro i _
                    ring
                  · rw [mul_sum]
                    apply sum_congr rfl
                    intro i _
                    ring
                _ = 2 ^ (q - 1) * ((∑ x : X, ν x * |f x + 1| ^ q) + 1) := by
                  rw [hνmass]
                  ring
        _ ≤ (2 : ℝ) ^ (q - 1) * ((2 : ℝ) ^ q + 1) := by
          gcongr
        _ ≤ (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ (q + 1) := by
          gcongr
          calc
            (2 : ℝ) ^ q + 1 ≤ (2 : ℝ) ^ q + (2 : ℝ) ^ q := by
              gcongr
              exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
            _ = (2 : ℝ) ^ (q + 1) := by rw [pow_succ]; ring
        _ = (2 : ℝ) ^ (2 * q) := by rw [← pow_add]; congr 1; omega
    have hmassT : (ε / 8) ^ (2 * p) ≤ ∑ i ∈ T, ν i := by
      have hfq' : weightedAbsMoment ν f (2 * p) ≤ (2 : ℝ) ^ (4 * p) := by
        convert hfq using 1 <;> simp [q] <;> omega
      have hcs' :
          ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 ≤
            (∑ i ∈ T, ν i) * (2 : ℝ) ^ (4 * p) :=
        hCSabs.trans (mul_le_mul_of_nonneg_left hfq' (sum_nonneg fun i _ ↦ hν i))
      have hden : (16 : ℝ) * (2 : ℝ) ^ (4 * p) ≤ (8 : ℝ) ^ (2 * p) := by
        have h16 : (16 : ℝ) ≤ 4 ^ p := by
          calc
            (16 : ℝ) = 4 ^ 2 := by norm_num
            _ ≤ 4 ^ p := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (by omega)
        rw [show (2 : ℝ) ^ (4 * p) = 16 ^ p by rw [pow_mul]; norm_num,
          show (8 : ℝ) ^ (2 * p) = 64 ^ p by rw [pow_mul]; norm_num]
        calc
          (16 : ℝ) * 16 ^ p ≤ 4 ^ p * 16 ^ p :=
            mul_le_mul_of_nonneg_right h16 (pow_nonneg (by norm_num) p)
          _ = 64 ^ p := by rw [← mul_pow]; norm_num
      rw [div_pow]
      apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 8) (2 * p))).2
      have hscaled := mul_le_mul_of_nonneg_left hcs' (by norm_num : (0 : ℝ) ≤ 16)
      calc
        ε ^ (2 * p) = 16 * ((4 : ℝ)⁻¹ * ε ^ p) ^ 2 := by
          rw [show 2 * p = p + p by omega, pow_add, pow_two]
          ring
        _ ≤ 16 * ((∑ i ∈ T, ν i) * (2 : ℝ) ^ (4 * p)) := hscaled
        _ = (∑ i ∈ T, ν i) * (16 * (2 : ℝ) ^ (4 * p)) := by ring
        _ ≤ (∑ i ∈ T, ν i) * (8 : ℝ) ^ (2 * p) :=
          mul_le_mul_of_nonneg_left hden (sum_nonneg fun i _ ↦ hν i)
    let m : ℕ := unbalancingMultiplier ε
    have hmpos : 0 < m := unbalancingMultiplier_pos hε₀
    have hm_spec : 60 / ε ^ 2 ≤ (m : ℝ) := by
      simpa [m] using unbalancingMultiplier_spec hε₀
    have hratio :
        1 + ε / 6 ≤ (1 + 3 * ε / 4) / (1 + ε / 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 1 + ε / 2)).2
      nlinarith
    have hratio_pow :
        8 / ε ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ m := by
      calc
        8 / ε ≤ 1 + (m : ℝ) * (ε / 6) := by
          have := mul_le_mul_of_nonneg_right hm_spec (by positivity : 0 ≤ ε / 6)
          field_simp at this ⊢
          nlinarith [sq_pos_of_pos hε₀]
        _ ≤ (1 + ε / 6) ^ m := one_add_mul_le_pow (by linarith) m
        _ ≤ ((1 + 3 * ε / 4) / (1 + ε / 2)) ^ m :=
          pow_le_pow_left₀ (by positivity) hratio m
    have hratio_mul :
        (1 + ε / 2) ^ m ≤ (ε / 8) * (1 + 3 * ε / 4) ^ m := by
      have hdenpos : 0 < (1 + ε / 2) ^ m := pow_pos (by positivity) m
      rw [div_pow] at hratio_pow
      have hcross := (le_div_iff₀ hdenpos).1 hratio_pow
      calc
        (1 + ε / 2) ^ m =
            (ε / 8) * ((8 / ε) * (1 + ε / 2) ^ m) := by field_simp
        _ ≤ (ε / 8) * (1 + 3 * ε / 4) ^ m :=
          mul_le_mul_of_nonneg_left hcross (by positivity)
    have hpower :
        (1 + ε / 2) ^ (2 * p * m) ≤
          (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := by
      calc
        (1 + ε / 2) ^ (2 * p * m) = ((1 + ε / 2) ^ m) ^ (2 * p) := by
          rw [← pow_mul, Nat.mul_comm m (2 * p)]
        _ ≤ ((ε / 8) * (1 + 3 * ε / 4) ^ m) ^ (2 * p) :=
          pow_le_pow_left₀ (by positivity) hratio_mul (2 * p)
        _ = (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm m (2 * p)]
    have heven : Even (2 * p * m) := by
      simpa [Nat.mul_assoc] using even_two_mul (p * m)
    refine ⟨2 * p * m, by positivity, heven, ?_, ?_⟩
    · simp [unbalancingExponent, m]
    · calc
        (1 + ε / 2) ^ (2 * p * m) ≤
            (ε / 8) ^ (2 * p) * (1 + 3 * ε / 4) ^ (2 * p * m) := hpower
        _ ≤ (∑ i ∈ T, ν i) * (1 + 3 * ε / 4) ^ (2 * p * m) :=
          mul_le_mul_of_nonneg_right hmassT (pow_nonneg (by positivity) _)
        _ = ∑ i ∈ T, ν i * (1 + 3 * ε / 4) ^ (2 * p * m) := by
          rw [← sum_mul]
        _ ≤ ∑ i ∈ T, ν i * |(f + 1) i| ^ (2 * p * m) := by
          apply sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_left _ (hν i)
          apply pow_le_pow_left₀ (by positivity) _ _
          have hi' : 3 / 4 * ε ≤ f i := by simpa [T] using hi
          have hf1 : 0 ≤ (f + 1) i := by
            simp only [Pi.add_apply, Pi.one_apply]
            nlinarith
          rw [abs_of_nonneg hf1]
          simp only [Pi.add_apply, Pi.one_apply]
          nlinarith
        _ ≤ weightedAbsMoment ν (f + 1) (2 * p * m) := by
          unfold weightedAbsMoment
          apply sum_le_sum_of_subset_of_nonneg (subset_univ T)
          intro i _ _
          exact mul_nonneg (hν i) (pow_nonneg (abs_nonneg _) _)
          
end Moments

section PhysicalUnbalancing

open Fintype _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped ComplexConjugate ComplexOrder _root_.ENNReal

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Physical-space positivity of every moment.  This is Bloom--Sisask Lemma 7:
autocorrelation representations of both the function and the weight turn the
moment into a finite sum of complex squared norms. -/
theorem physical_pow_inner_nonneg {ν : G → ℝ≥0} {f : G → ℝ} {g h : G → ℂ}
    (hf : g ○ᵈ g = (↑) ∘ f) (hν : h ○ᵈ h = (↑) ∘ ν) (k : ℕ) :
    (0 : ℝ) ≤ ⟪(↑) ∘ ν, f ^ k⟫_[ℝ] :=
  _root_.Erdos140.pow_inner_nonneg hf hν k

end PhysicalUnbalancing

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BohrStopping.lean` -/

section
/-!
# Maximal regular-Bohr restriction chains

This file contains the finite stopping argument used by the balanced
restriction step of the Kelley--Meka proof.  Unlike the numerical state in
`DensityIteration.lean`, every node below contains an actual subset of an
actual, scale-regular finite Bohr carrier.

The analytic density-increment lemma is represented by the predicate
`ProducesIncrement`: whenever a proposed stopping inequality is bad, it
produces another regular restriction with controlled density, rank, and
cardinality.  The main theorem proves that this process stops, and returns
all three accumulated bounds.  The final specialization records explicitly
that an eleventh-power loss at each of at most `L + 1` stages has total
twelfth-power cost.
-/

open _root_.Finset
open scoped _root_.NNReal

namespace BohrStopping

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- One node of the regular-Bohr restriction iteration.

The ambient finite set is `(bohr.dilate outer).carrier`; `inner` is the shell
width at which this carrier is certified to be coarsely regular. -/
structure RegularRestriction (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] where
  bohr : BohrData G
  outer : ℝ≥0
  inner : ℝ≥0
  regular : 0 < inner ∧ inner ≤ outer ∧
    (bohr.dilate (outer + inner)).carrier.card ≤
      2 * (bohr.dilate (outer - inner)).carrier.card
  set : Finset G
  nonempty : set.Nonempty
  subset_carrier : set ⊆ (bohr.dilate outer).carrier

namespace RegularRestriction

/-- The finite regular Bohr carrier at a restriction node. -/
def ambient (s : RegularRestriction G) : Finset G :=
  (s.bohr.dilate s.outer).carrier

/-- The relative density of the restricted set in its Bohr carrier. -/
def density (s : RegularRestriction G) : ℝ :=
  (s.set.card : ℝ) / s.ambient.card

/-- Rank of the ambient Bohr datum.  Dilation does not change this rank. -/
def rank (s : RegularRestriction G) : ℕ := s.bohr.rank

/-- Cardinality of the ambient regular Bohr carrier. -/
def card (s : RegularRestriction G) : ℕ := s.ambient.card

lemma ambient_nonempty (s : RegularRestriction G) : s.ambient.Nonempty :=
  (s.bohr.dilate s.outer).carrier_nonempty

lemma card_pos (s : RegularRestriction G) : 0 < s.card :=
  s.ambient_nonempty.card_pos

lemma density_pos (s : RegularRestriction G) : 0 < s.density := by
  exact div_pos (by exact_mod_cast s.nonempty.card_pos)
    (by exact_mod_cast s.ambient_nonempty.card_pos)

lemma density_nonneg (s : RegularRestriction G) : 0 ≤ s.density :=
  s.density_pos.le

lemma density_le_one (s : RegularRestriction G) : s.density ≤ 1 := by
  rw [density, div_le_one (by exact_mod_cast s.ambient_nonempty.card_pos)]
  exact_mod_cast Finset.card_le_card s.subset_carrier

end RegularRestriction

/-- A controlled density-increment move between actual regular Bohr
restrictions.  The size inequality is deliberately stated after casting to
`ℝ`, because its natural loss factor is exponential. -/
def IsControlledIncrement (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (s t : RegularRestriction G) : Prop :=
  q * s.density ≤ t.density ∧
    t.rank ≤ s.rank + rankCost ∧
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- A chain with exactly `n` controlled restriction moves. -/
inductive ControlledChain (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) :
    ℕ → RegularRestriction G → RegularRestriction G → Prop
  | nil (s : RegularRestriction G) : ControlledChain q rankCost sizeCost 0 s s
  | cons {n : ℕ} {s t u : RegularRestriction G}
      (hst : IsControlledIncrement q rankCost sizeCost s t)
      (htu : ControlledChain q rankCost sizeCost n t u) :
      ControlledChain q rankCost sizeCost (n + 1) s u

namespace ControlledChain

/-- Density multiplies along a controlled chain. -/
theorem density_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    (hq : 0 ≤ q) {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    q ^ n * s.density ≤ t.density := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      have hqpow : 0 ≤ q ^ n := pow_nonneg hq n
      calc
        q ^ (n + 1) * s.density = q ^ n * (q * s.density) := by
          rw [pow_succ]
          ring
        _ ≤ q ^ n * t.density :=
          mul_le_mul_of_nonneg_left hst.1 hqpow
        _ ≤ u.density := ih

/-- Rank costs add along a controlled chain. -/
theorem rank_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    t.rank ≤ s.rank + n * rankCost := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      calc
        u.rank ≤ t.rank + n * rankCost := ih
        _ ≤ (s.rank + rankCost) + n * rankCost :=
          Nat.add_le_add_right hst.2.1 (n * rankCost)
        _ = s.rank + (n + 1) * rankCost := by
          simp only [Nat.add_mul, one_mul]
          omega

/-- Exponential cardinality losses multiply along a controlled chain. -/
theorem card_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    Real.exp (-(n : ℝ) * sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ) := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * sizeCost) :=
        (Real.exp_pos _).le
      calc
        Real.exp (-((n + 1 : ℕ) : ℝ) * sizeCost) * (s.card : ℝ) =
            Real.exp (-(n : ℝ) * sizeCost) *
              (Real.exp (-sizeCost) * (s.card : ℝ)) := by
          rw [show -((n + 1 : ℕ) : ℝ) * sizeCost =
              (-(n : ℝ) * sizeCost) + (-sizeCost) by
            push_cast
            ring,
            Real.exp_add]
          ring
        _ ≤ Real.exp (-(n : ℝ) * sizeCost) * (t.card : ℝ) :=
          mul_le_mul_of_nonneg_left hst.2.2 hexp_nonneg
        _ ≤ (u.card : ℝ) := ih

end ControlledChain

/-- The exact interface supplied by a density-increment proposition: every
node at which `Bad` holds admits another controlled regular restriction. -/
def ProducesIncrement (Bad : RegularRestriction G → Prop)
    (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) : Prop :=
  ∀ s : RegularRestriction G, Bad s →
    ∃ t : RegularRestriction G,
      IsControlledIncrement q rankCost sizeCost s t

/-- The dyadic scale condition on the initial relative density. -/
def OnDyadicScale (L : ℕ) (density : ℝ) : Prop :=
  1 / (2 : ℝ) ^ L ≤ density

end

end BohrStopping

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BalancedRestriction.lean` -/

section
/-!
# The balanced-restriction stopping bridge

The balanced Bohr restriction argument uses three controlled changes of exponent which
are easy to blur in an informal proof.  Starting from a positive natural
exponent `p`, we first pass to the even exponent `q = 2p`.  The checked
power-moment form of unbalancing takes an odd exponent at least five, so we
promote once more to `qOdd = 2q + 3`.  Localized unbalancing can then return an
arbitrary positive exponent `r`; the stopping theorem is run at the fixed even exponent

`Q = unbalancingExponent (ε / 2) qOdd`.

This file proves the probability-space `L^p` monotonicity needed for both
changes of exponent and packages the final contradiction.  Its constants
match the audited proof: comparison loses a factor two, localized
unbalancing gains `1 + ε / 8`, and the stopping estimate has the same strict
`1 + ε / 8` threshold.

The Bohr-set construction supplies the four analytic hypotheses of
`balanced_convolution_of_stopping`; the theorem below contains no hidden
choice principle or unproved declaration.
-/

open _root_.Finset
open scoped BigOperators

namespace BalancedRestriction

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A nonnegative weight of total mass one on a finite type. -/
structure ProbabilityWeight (ν : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ν x
  sum_eq_one : ∑ x, ν x = 1

/-- The natural-exponent weighted `L^p` norm.  Exponent zero is assigned the
value zero; every theorem using this definition assumes a positive exponent. -/
noncomputable def weightedLpNorm (ν f : X → ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else
    (weightedAbsMoment ν f p) ^ (1 / (p : ℝ))

omit [DecidableEq X] in
lemma weightedLpNorm_of_pos (ν f : X → ℝ) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f p =
      (weightedAbsMoment ν f p) ^ (1 / (p : ℝ)) := by
  simp [weightedLpNorm, hp.ne']

lemma weightedLpNorm_nonneg {ν : X → ℝ} (hν : ProbabilityWeight ν)
    (f : X → ℝ) (p : ℕ) :
    0 ≤ weightedLpNorm ν f p := by
  unfold weightedLpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (weightedAbsMoment_nonneg hν.nonneg p) _

lemma weightedLpNorm_pow {ν f : X → ℝ} (hν : ProbabilityWeight ν)
    {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f p ^ p = weightedAbsMoment ν f p := by
  rw [weightedLpNorm_of_pos _ _ hp, ← Real.rpow_natCast,
    ← Real.rpow_mul (weightedAbsMoment_nonneg hν.nonneg p)]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp
  simp

private lemma abs_pow_rpow_div {x : ℝ} {p q : ℕ} (hp : 0 < p) :
    (|x| ^ p) ^ ((q : ℝ) / (p : ℝ)) = |x| ^ q := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (abs_nonneg x)]
  rw [← Real.rpow_natCast]
  congr 1
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- Generalized-mean inequality for finite probability weights, in the exact
form used by the balanced-restriction proof. -/
theorem weightedLpNorm_mono_exponent
    {ν f : X → ℝ} (hν : ProbabilityWeight ν)
    {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    weightedLpNorm ν f p ≤ weightedLpNorm ν f q := by
  have hq : 0 < q := hp.trans_le hpq
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpqR : (p : ℝ) ≤ q := by exact_mod_cast hpq
  have hratio : (1 : ℝ) ≤ (q : ℝ) / (p : ℝ) := by
    exact (le_div_iff₀ hpR).2 (by simpa using hpqR)
  have hmomentP : 0 ≤ weightedAbsMoment ν f p :=
    weightedAbsMoment_nonneg hν.nonneg p
  have hmomentQ : 0 ≤ weightedAbsMoment ν f q :=
    weightedAbsMoment_nonneg hν.nonneg q
  have hjensen :
      (weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ)) ≤
        weightedAbsMoment ν f q := by
    have h := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset X) ν (fun x ↦ |f x| ^ p)
      (fun x _ ↦ hν.nonneg x) (by simpa using hν.sum_eq_one)
      (fun x _ ↦ pow_nonneg (abs_nonneg _) _) hratio
    simpa only [weightedAbsMoment, mem_univ, abs_pow_rpow_div hp] using h
  rw [weightedLpNorm_of_pos _ _ hp, weightedLpNorm_of_pos _ _ hq]
  have hleft :
      0 ≤ (weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ)) :=
    Real.rpow_nonneg hmomentP _
  have hroot := Real.rpow_le_rpow hleft hjensen
    (div_nonneg zero_le_one hqR.le)
  calc
    (weightedAbsMoment ν f p) ^ (1 / (p : ℝ)) =
        ((weightedAbsMoment ν f p) ^ ((q : ℝ) / (p : ℝ))) ^
          (1 / (q : ℝ)) := by
      rw [← Real.rpow_mul hmomentP]
      congr 1
      field_simp
    _ ≤ (weightedAbsMoment ν f q) ^ (1 / (q : ℝ)) := hroot

/-- Taking a positive natural root weakens a factor two by at most a factor
two.  This is the root adapter used after the moment-form convolution
comparison theorem. -/
theorem weightedLpNorm_le_two_of_moment_le_two
    {muWeight ν f g : X → ℝ} (hmuWeight : ProbabilityWeight muWeight) (hν : ProbabilityWeight ν)
    {p : ℕ} (hp : 0 < p)
    (hmoment : weightedAbsMoment muWeight f p ≤ 2 * weightedAbsMoment ν g p) :
    weightedLpNorm muWeight f p ≤ 2 * weightedLpNorm ν g p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have ha : 0 ≤ (1 / (p : ℝ)) := by positivity
  have haone : (1 / (p : ℝ)) ≤ 1 := by
    rw [div_le_one hpR]
    exact_mod_cast hp
  have hmuWeightmoment : 0 ≤ weightedAbsMoment muWeight f p :=
    weightedAbsMoment_nonneg hmuWeight.nonneg p
  have hνmoment : 0 ≤ weightedAbsMoment ν g p :=
    weightedAbsMoment_nonneg hν.nonneg p
  rw [weightedLpNorm_of_pos _ _ hp, weightedLpNorm_of_pos _ _ hp]
  calc
    (weightedAbsMoment muWeight f p) ^ (1 / (p : ℝ)) ≤
        (2 * weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow hmuWeightmoment hmoment ha
    _ = (2 : ℝ) ^ (1 / (p : ℝ)) *
        (weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hνmoment]
    _ ≤ 2 * (weightedAbsMoment ν g p) ^ (1 / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hνmoment _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) haone

/-- The first, even exponent used in the proof. -/
def comparisonExponent (p : ℕ) : ℕ := 2 * p

theorem comparisonExponent_even (p : ℕ) : Even (comparisonExponent p) := by
  exact ⟨p, by simp [comparisonExponent, two_mul]⟩

theorem le_comparisonExponent {p : ℕ} (hp : 0 < p) :
    p ≤ comparisonExponent p := by
  simp only [comparisonExponent]
  omega

/-- The odd exponent at which the power-moment unbalancing lemma is applied. -/
def unbalancingInputExponent (p : ℕ) : ℕ :=
  2 * comparisonExponent p + 3

theorem unbalancingInputExponent_odd (p : ℕ) :
    Odd (unbalancingInputExponent p) := by
  simp [unbalancingInputExponent, comparisonExponent, Nat.odd_iff]

theorem five_le_unbalancingInputExponent {p : ℕ} (hp : 0 < p) :
    5 ≤ unbalancingInputExponent p := by
  simp only [unbalancingInputExponent, comparisonExponent]
  omega

theorem comparisonExponent_le_unbalancingInputExponent (p : ℕ) :
    comparisonExponent p ≤ unbalancingInputExponent p := by
  simp only [unbalancingInputExponent]
  omega

/-- The second exponent promotion in the corrected argument: the even
comparison exponent may be promoted to the odd unbalancing input on any
finite probability space. -/
theorem weightedLpNorm_comparison_le_unbalancingInput
    {ν f : X → ℝ} (hν : ProbabilityWeight ν) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm ν f (comparisonExponent p) ≤
      weightedLpNorm ν f (unbalancingInputExponent p) := by
  apply weightedLpNorm_mono_exponent hν
  · exact Nat.mul_pos (by norm_num) hp
  · exact comparisonExponent_le_unbalancingInputExponent p

/-- The fixed even stopping exponent.  The argument applies unbalancing with
error `ε / 2`, so this definition records that choice literally. -/
noncomputable def stoppingExponent (ε : ℝ) (p : ℕ) : ℕ :=
  unbalancingExponent (ε / 2) (unbalancingInputExponent p)

theorem stoppingExponent_even (ε : ℝ) (p : ℕ) :
    Even (stoppingExponent ε p) := by
  exact unbalancingExponent_even _ _

theorem stoppingExponent_pos {ε : ℝ} {p : ℕ}
    (hε : 0 < ε) (hp : 0 < p) :
    0 < stoppingExponent ε p := by
  apply unbalancingExponent_pos (p := unbalancingInputExponent p)
  · positivity
  · have hfive := five_le_unbalancingInputExponent hp
    omega

/-- An explicit bound showing that the fixed stopping exponent is only a
constant (depending on `ε`) times the original exponent. -/
theorem stoppingExponent_eq (ε : ℝ) (p : ℕ) :
    stoppingExponent ε p =
      (8 * p + 6) * unbalancingMultiplier (ε / 2) := by
  unfold stoppingExponent unbalancingExponent unbalancingInputExponent
    comparisonExponent
  ring

theorem stoppingExponent_le_const_mul {ε : ℝ} {p : ℕ} (hp : 0 < p) :
    stoppingExponent ε p ≤
      14 * unbalancingMultiplier (ε / 2) * p := by
  rw [stoppingExponent_eq]
  have hlinear : 8 * p + 6 ≤ 14 * p := by omega
  have h := Nat.mul_le_mul_right (unbalancingMultiplier (ε / 2)) hlinear
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- The exact-scaling core of localized unbalancing.  In the Bohr argument
the identity `positiveCorr = mainTerm * (1 + f)` holds up to a small boundary
error; regularity absorbs that error before this lemma is invoked.  This
theorem records the error-free analytic step and, importantly, returns a
*positive even* exponent, so subsequent `L^p` promotion is legitimate. -/
theorem unbalancing_of_exact_scaling
    {ν : X → ℝ} (hν : ProbabilityWeight ν)
    {f positiveCorr : X → ℝ} {η mainTerm : ℝ}
    (hη₀ : 0 < η) (hη₁ : η ≤ 1) (hmain : 0 < mainTerm)
    {p : ℕ} (hp : 5 ≤ p) (hpodd : Odd p)
    (hmom : ∀ k : ℕ, 0 ≤ weightedMoment ν f k)
    (hlarge : η ^ p ≤ weightedAbsMoment ν f p)
    (hscale : ∀ x, positiveCorr x = mainTerm * (1 + f x)) :
    ∃ r : ℕ, 0 < r ∧ Even r ∧ r ≤ unbalancingExponent η p ∧
      (1 + η / 2) * mainTerm ≤ weightedLpNorm ν positiveCorr r := by
  obtain ⟨r, hr, hreven, hrBound, hunbalanced⟩ :=
    unbalancing_of_nonnegative_moments hν.nonneg hν.sum_eq_one hmom
      hη₀ hη₁ hp hpodd hlarge
  refine ⟨r, hr, hreven, hrBound, ?_⟩
  have hmomentScale :
      weightedAbsMoment ν positiveCorr r =
        mainTerm ^ r * weightedAbsMoment ν (f + 1) r := by
    unfold weightedAbsMoment
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro x _
    rw [hscale x, abs_mul, abs_of_pos hmain, mul_pow]
    simp only [Pi.add_apply, Pi.one_apply]
    ring_nf
  have hpower :
      ((1 + η / 2) * mainTerm) ^ r ≤
        weightedAbsMoment ν positiveCorr r := by
    rw [hmomentScale, mul_pow]
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right hunbalanced (pow_nonneg hmain.le r))
  rw [weightedLpNorm_of_pos _ _ hr]
  have hbase : 0 ≤ (1 + η / 2) * mainTerm := by positivity
  have hroot := Real.rpow_le_rpow (pow_nonneg hbase r) hpower
    (by positivity : 0 ≤ (r : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hbase hr.ne'] at hroot
  simpa [one_div] using hroot

/-- **Even-exponent promotion and the `1/8` contradiction.**

`balanced` is the balanced convolution, `corr` its autocorrelation after the
comparison step, and `positiveCorr` the unbalanced positive correlation.  In
the Bohr application the weights `muWeight` and `ν` are the corresponding normalized
Bohr probability weights.

The four analytic inputs are stated separately so their roles are visible:

* `hcomparison` is the factor-two convolution comparison at the even exponent;
* `hunbalance` is localized unbalancing, returning some positive `r ≤ Q`;
* `hstopping` is the strict stopping estimate at `Q`.

The conclusion is the desired balanced bound at the original exponent. -/
theorem balanced_convolution_of_stopping
    {muWeight ν : X → ℝ} (hmuWeight : ProbabilityWeight muWeight) (hν : ProbabilityWeight ν)
    {balanced corr positiveCorr : X → ℝ}
    {ε mainTerm : ℝ} (hε : 0 < ε) (hmain : 0 < mainTerm)
    {p : ℕ} (hp : 0 < p)
    (hcomparison :
      weightedLpNorm muWeight balanced (comparisonExponent p) ≤
        2 * weightedLpNorm ν corr (comparisonExponent p))
    (hunbalance :
      ε * mainTerm / 2 < weightedLpNorm ν corr (comparisonExponent p) →
        ∃ r : ℕ, 0 < r ∧ r ≤ stoppingExponent ε p ∧
          (1 + ε / 8) * mainTerm ≤ weightedLpNorm ν positiveCorr r)
    (hstopping :
      weightedLpNorm ν positiveCorr (stoppingExponent ε p) <
        (1 + ε / 8) * mainTerm) :
    weightedLpNorm muWeight balanced p ≤ ε * mainTerm := by
  have hεmain : 0 < ε * mainTerm := mul_pos hε hmain
  by_contra hbound
  have hfail : ε * mainTerm < weightedLpNorm muWeight balanced p := lt_of_not_ge hbound
  have hpromoteBalanced :
      weightedLpNorm muWeight balanced p ≤
        weightedLpNorm muWeight balanced (comparisonExponent p) :=
    weightedLpNorm_mono_exponent hmuWeight hp (le_comparisonExponent hp)
  have hcorrLarge :
      ε * mainTerm / 2 < weightedLpNorm ν corr (comparisonExponent p) := by
    nlinarith [hεmain, hfail.trans_le hpromoteBalanced, hcomparison,
      weightedLpNorm_nonneg hν corr (comparisonExponent p)]
  obtain ⟨r, hr, hrQ, hunbalanced⟩ := hunbalance hcorrLarge
  have hpromotePositive :
      weightedLpNorm ν positiveCorr r ≤
        weightedLpNorm ν positiveCorr (stoppingExponent ε p) :=
    weightedLpNorm_mono_exponent hν hr hrQ
  exact (not_lt_of_ge (hunbalanced.trans hpromotePositive)) hstopping

end BalancedRestriction

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/FiniteConvolution.lean` -/

section
/-!
# Normalized convolution on a finite additive group

The normalizations here are probability normalizations: `normalizedIndicator A`
has value `1 / |A|` on `A`, and convolution is defined using an ordinary
(unnormalized) finite sum.  Thus every nonempty normalized indicator, and the
convolution of two such indicators, has total mass one.
-/

open _root_.Finset _root_.Function
open scoped BigOperators translate

noncomputable section

section Definitions

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The probability-normalized indicator of a finite set.  It is identically
zero when the set is empty. -/
def normalizedIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (#A : ℝ)⁻¹ else 0

/-- Convolution with counting measure on a finite additive group. -/
def normalizedConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

/-- Difference convolution with counting measure.  At `x` it correlates `f`
with the translate `y ↦ g (y - x)`. -/
def normalizedDifferenceConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (y - x)

/-- The counting-measure inner product of two real functions on a finite group. -/
def finiteInner (f g : G → ℝ) : ℝ :=
  ∑ x : G, f x * g x

@[simp]
theorem normalizedIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    normalizedIndicator A x = (#A : ℝ)⁻¹ := by
  simp [normalizedIndicator, hx]

@[simp]
theorem normalizedIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    normalizedIndicator A x = 0 := by
  simp [normalizedIndicator, hx]

theorem normalizedIndicator_nonneg (A : Finset G) (x : G) :
    0 ≤ normalizedIndicator A x := by
  unfold normalizedIndicator
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl

theorem normalizedIndicator_pos_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    0 < normalizedIndicator A x ↔ x ∈ A := by
  unfold normalizedIndicator
  split_ifs with hx
  · simp only [hx, iff_true]
    exact inv_pos.mpr (Nat.cast_pos.mpr hA.card_pos)
  · simp [hx]

theorem normalizedIndicator_ne_zero_iff {A : Finset G} (hA : A.Nonempty) (x : G) :
    normalizedIndicator A x ≠ 0 ↔ x ∈ A := by
  unfold normalizedIndicator
  split_ifs with hx
  · simp [hx, hA.card_ne_zero]
  · simp [hx]

theorem sum_normalizedIndicator {A : Finset G} (hA : A.Nonempty) :
    ∑ x : G, normalizedIndicator A x = 1 := by
  change (∑ x ∈ (univ : Finset G), if x ∈ A then (#A : ℝ)⁻¹ else 0) = 1
  rw [← Finset.sum_filter]
  have hfilter : univ.filter (fun x : G ↦ x ∈ A) = A := by ext; simp
  rw [hfilter]
  simp [hA.card_ne_zero]

theorem normalizedConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ normalizedConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (z - x))

theorem normalizedDifferenceConvolution_nonneg {f g : G → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (z : G) :
    0 ≤ normalizedDifferenceConvolution f g z := by
  exact sum_nonneg fun x _ ↦ mul_nonneg (hf x) (hg (x - z))

/-- Convolution of normalized indicators is the normalized cardinality of a
representation fiber. -/
theorem normalizedConvolution_indicators_eq_card (A B : Finset G) (x : G) :
    normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (#(A.filter fun y ↦ x - y ∈ B) : ℝ) * (#A : ℝ)⁻¹ * (#B : ℝ)⁻¹ := by
  have hfilter : (univ.filter fun y : G ↦ x - y ∈ B) ∩ A =
      A.filter fun y ↦ x - y ∈ B := by
    ext y
    simp [and_comm]
  simp [normalizedConvolution, normalizedIndicator, ← Finset.sum_filter,
    mul_assoc, mul_left_comm, hfilter]

/-- A one-variable representation fiber is in bijection with the pairs counted
by Mathlib's additive convolution. -/
theorem card_filter_sub_mem_eq_addConvolution (A B : Finset G) (x : G) :
    #(A.filter fun y ↦ x - y ∈ B) = A.addConvolution B x := by
  unfold Finset.addConvolution
  refine Finset.card_nbij' (fun y ↦ (y, x - y)) (fun ab ↦ ab.1) ?_ ?_ ?_ ?_
  · intro y hy
    change y ∈ A.filter (fun y ↦ x - y ∈ B) at hy
    change (y, x - y) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x)
    rw [mem_filter] at hy ⊢
    exact ⟨mem_product.mpr hy, by simp⟩
  · rintro ⟨a, b⟩ hab
    change (a, b) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x) at hab
    change a ∈ A.filter (fun y ↦ x - y ∈ B)
    simp only [mem_filter, mem_product] at hab ⊢
    rcases hab with ⟨⟨ha, hb⟩, hsum⟩
    refine ⟨ha, ?_⟩
    have hxb : x - a = b := by
      rw [← hsum]
      simp [add_comm]
    simpa [hxb] using hb
  · intro y _
    rfl
  · rintro ⟨a, b⟩ hab
    change (a, b) ∈ (A ×ˢ B).filter (fun ab ↦ ab.1 + ab.2 = x) at hab
    simp only [mem_filter, mem_product] at hab
    rcases hab with ⟨-, hsum⟩
    have hxb : x - a = b := by
      rw [← hsum]
      simp [add_comm]
    simp [hxb]

theorem normalizedConvolution_indicators_eq_addConvolution (A B : Finset G) (x : G) :
    normalizedConvolution (normalizedIndicator A) (normalizedIndicator B) x =
      (A.addConvolution B x : ℝ) * (#A : ℝ)⁻¹ * (#B : ℝ)⁻¹ := by
  rw [normalizedConvolution_indicators_eq_card, card_filter_sub_mem_eq_addConvolution]

end Definitions

section Algebra

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Convolution is commutative on an additive commutative group. -/
theorem normalizedConvolution_comm (f g : G → ℝ) :
    normalizedConvolution f g = normalizedConvolution g f := by
  funext x
  rw [normalizedConvolution, normalizedConvolution]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ ?_
  simp [mul_comm]

/-- The total mass of a convolution is the product of the two total masses. -/
theorem sum_normalizedConvolution (f g : G → ℝ) :
    ∑ x : G, normalizedConvolution f g x = (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [normalizedConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight y) _ _ fun x ↦ by simp

/-- The total mass of a difference convolution is likewise multiplicative. -/
theorem sum_normalizedDifferenceConvolution (f g : G → ℝ) :
    ∑ x : G, normalizedDifferenceConvolution f g x =
      (∑ x : G, f x) * ∑ x : G, g x := by
  simp_rw [normalizedDifferenceConvolution, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft y) _ _ fun x ↦ by simp

end Algebra

section APCounting

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The number of ordered solutions `a₁ + a₂ = c + c` with both endpoints in
`A` and the middle term in `C`. -/
def mixedThreeAPCount (A C : Finset G) : ℕ :=
  #(((A ×ˢ A) ×ˢ C).filter fun x ↦ x.1.1 + x.1.2 = x.2 + x.2)

/-- The mixed count is the sum of endpoint representation counts over its
allowed middle terms. -/
theorem mixedThreeAPCount_eq_sum_addConvolution (A C : Finset G) :
    mixedThreeAPCount A C = ∑ c ∈ C, A.addConvolution A (c + c) := by
  unfold mixedThreeAPCount Finset.addConvolution
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  calc
    (∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ C, if a + b = c + c then 1 else 0) =
        ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ A, if a + b = c + c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ A, if a + b = c + c then 1 else 0 := by
      rw [Finset.sum_comm]

/-- Ordered three-term progressions can be counted by summing the additive
convolution fiber at `b+b` over all possible middle terms `b`. -/
theorem threeAPCount_eq_sum_addConvolution (A : Finset G) :
    threeAPCount A = ∑ b ∈ A, A.addConvolution A (b + b) := by
  unfold threeAPCount Finset.addConvolution
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  conv_lhs => rw [Finset.sum_comm]

/-- If doubling is injective, the normalized convolution/indicator inner
product is exactly the ordered three-term-progression count divided by `|A|³`. -/
theorem finiteInner_convolution_doubleIndicator {A : Finset G}
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    finiteInner (normalizedConvolution (normalizedIndicator A) (normalizedIndicator A))
        (normalizedIndicator (A.image fun x ↦ x + x)) =
      (threeAPCount A : ℝ) * (#A : ℝ)⁻¹ ^ 3 := by
  let D : Finset G := A.image fun x ↦ x + x
  have hcardD : #D = #A := by
    dsimp [D]
    exact card_image_of_injective _ hdouble
  have hrestrict (F : G → ℝ) :
      (∑ z : G, F z * normalizedIndicator D z) =
        ∑ z ∈ D, F z * (#D : ℝ)⁻¹ := by
    change (∑ z : G, F z * (if z ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun z : G ↦ z ∈ D) = D := by ext; simp
    rw [hfilter]
  have hsumNat : ∑ z ∈ D, A.addConvolution A z = threeAPCount A := by
    rw [threeAPCount_eq_sum_addConvolution]
    dsimp [D]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hdouble hab
  have hsumReal : ∑ z ∈ D, (A.addConvolution A z : ℝ) = (threeAPCount A : ℝ) := by
    exact_mod_cast hsumNat
  rw [finiteInner, hrestrict]
  simp_rw [normalizedConvolution_indicators_eq_addConvolution]
  rw [hcardD]
  calc
    (∑ z ∈ D,
        ((A.addConvolution A z : ℝ) * (#A : ℝ)⁻¹ * (#A : ℝ)⁻¹) * (#A : ℝ)⁻¹) =
        (∑ z ∈ D, (A.addConvolution A z : ℝ)) * (#A : ℝ)⁻¹ ^ 3 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z _
          simp only [pow_succ, pow_two]
          ac_rfl
    _ = (threeAPCount A : ℝ) * (#A : ℝ)⁻¹ ^ 3 := by
      rw [hsumReal]

/-- Mixed form of `finiteInner_convolution_doubleIndicator`: endpoints lie in
`A`, while the doubled middle term comes from `C`. -/
theorem finiteInner_convolution_mixedDoubleIndicator {A C : Finset G}
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    finiteInner (normalizedConvolution (normalizedIndicator A) (normalizedIndicator A))
        (normalizedIndicator (C.image fun x ↦ x + x)) =
      (mixedThreeAPCount A C : ℝ) * (#A : ℝ)⁻¹ ^ 2 * (#C : ℝ)⁻¹ := by
  let D : Finset G := C.image fun x ↦ x + x
  have hcardD : #D = #C := by
    dsimp [D]
    exact card_image_of_injective _ hdouble
  have hrestrict (F : G → ℝ) :
      (∑ z : G, F z * normalizedIndicator D z) =
        ∑ z ∈ D, F z * (#D : ℝ)⁻¹ := by
    change (∑ z : G, F z * (if z ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun z : G ↦ z ∈ D) = D := by ext; simp
    rw [hfilter]
  have hsumNat : ∑ z ∈ D, A.addConvolution A z = mixedThreeAPCount A C := by
    rw [mixedThreeAPCount_eq_sum_addConvolution]
    dsimp [D]
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hdouble hab
  have hsumReal : ∑ z ∈ D, (A.addConvolution A z : ℝ) = (mixedThreeAPCount A C : ℝ) := by
    exact_mod_cast hsumNat
  rw [finiteInner, hrestrict]
  simp_rw [normalizedConvolution_indicators_eq_addConvolution]
  rw [hcardD]
  have hpoint (z : G) :
      ((A.addConvolution A z : ℝ) * (#A : ℝ)⁻¹ * (#A : ℝ)⁻¹) * (#C : ℝ)⁻¹ =
        (A.addConvolution A z : ℝ) *
          ((#A : ℝ)⁻¹ * (#A : ℝ)⁻¹ * (#C : ℝ)⁻¹) := by ac_rfl
  simp_rw [hpoint]
  rw [← Finset.sum_mul, hsumReal]
  simp only [pow_two]
  ac_rfl

/-- Translation invariance of the AP equation gives the exact lifting used
after a local argument: if both local sets become subsets of `A` after
translation by `-t`, their mixed count is bounded by the AP count of `A`. -/
theorem mixedThreeAPCount_le_threeAPCount_of_sub_translate {A A' C : Finset G} (t : G)
    (hA : ∀ x ∈ A', x - t ∈ A) (hC : ∀ x ∈ C, x - t ∈ A) :
    mixedThreeAPCount A' C ≤ threeAPCount A := by
  unfold mixedThreeAPCount threeAPCount
  let f : ((G × G) × G) → ((G × G) × G) := fun x ↦
    ((x.1.1 - t, x.2 - t), x.1.2 - t)
  apply Finset.card_le_card_of_injOn f
  · rintro ⟨⟨a, c⟩, b⟩ habc
    change ((a, c), b) ∈ (((A' ×ˢ A') ×ˢ C).filter fun x ↦
      x.1.1 + x.1.2 = x.2 + x.2) at habc
    change ((a - t, b - t), c - t) ∈ (((A ×ˢ A) ×ˢ A).filter fun x ↦
      x.1.1 + x.2 = x.1.2 + x.1.2)
    simp only [mem_filter, mem_product] at habc ⊢
    rcases habc with ⟨⟨⟨ha, hc⟩, hb⟩, hrel⟩
    refine ⟨⟨⟨hA a ha, hC b hb⟩, hA c hc⟩, ?_⟩
    calc
      (a - t) + (c - t) = (a + c) - (t + t) := by
        simp only [sub_eq_add_neg, neg_add_rev]
        ac_rfl
      _ = (b + b) - (t + t) := congrArg (fun x ↦ x - (t + t)) hrel
      _ = (b - t) + (b - t) := by
        simp only [sub_eq_add_neg, neg_add_rev]
        ac_rfl
  · rintro ⟨⟨a, c⟩, b⟩ _ ⟨⟨a', c'⟩, b'⟩ _ heq
    have haSub : a - t = a' - t := congrArg (fun x ↦ x.1.1) heq
    have hbSub : b - t = b' - t := congrArg (fun x ↦ x.1.2) heq
    have hcSub : c - t = c' - t := congrArg (fun x ↦ x.2) heq
    have ha : a = a' := calc
      a = (a - t) + t := (sub_add_cancel a t).symm
      _ = (a' - t) + t := congrArg (fun x ↦ x + t) haSub
      _ = a' := sub_add_cancel a' t
    have hb : b = b' := calc
      b = (b - t) + t := (sub_add_cancel b t).symm
      _ = (b' - t) + t := congrArg (fun x ↦ x + t) hbSub
      _ = b' := sub_add_cancel b' t
    have hc : c = c' := calc
      c = (c - t) + t := (sub_add_cancel c t).symm
      _ = (c' - t) + t := congrArg (fun x ↦ x + t) hcSub
      _ = c' := sub_add_cancel c' t
    simp [ha, hb, hc]

end APCounting

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RegularBohr.lean` -/

section
/-!
# Regular scales for finite Bohr sets

The carrier of a dilated finite Bohr set is a monotone, integer-valued
function of the dilation parameter.  This file records two completely
elementary regular-value consequences of that fact.

* `exists_plateauRegularAt` is unconditional.  It finds a scale in `[1/2,1]`
  on which the carrier is literally constant in a (possibly very small, but
  explicit) neighbourhood.  Its proof uses `|G| + 1` adjacent intervals.
* `exists_coarselyRegularAt_of_card_growth` is the quantitative
  growth/pigeonhole form used together with a Bohr volumetric estimate.  If
  the cardinality grows by less than `2^n` between scales `1/2` and `1`, one
  of `n` adjacent shells grows by at most a factor two.

The exact plateau statement also gives exact translation invariance for
translations in the smaller Bohr carrier.  We state this both as a
symmetric-difference assertion and as an `L^1` assertion for the normalized
indicator used elsewhere in the Erdős 140 development.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal symmDiff

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Two elementary discrete growth lemmas -/

private lemma exists_adjacent_eq_of_bounded
    (N : ℕ) (f : ℕ → ℕ) (hf : Monotone f)
    (hpos : 1 ≤ f 0) (hbound : f (N + 1) ≤ N) :
    ∃ i ≤ N, f i = f (i + 1) := by
  by_contra! h
  have hadj : ∀ i ≤ N, f i < f (i + 1) := by
    intro i hi
    exact lt_of_le_of_ne (hf (Nat.le_succ i)) (h i hi)
  have hgrow : ∀ k ≤ N + 1, f 0 + k ≤ f k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkN : k ≤ N := by omega
        have hih := ih (by omega)
        have hstep := hadj k hkN
        omega
  have := hgrow (N + 1) (by omega)
  omega

private lemma exists_adjacent_double_le
    (n : ℕ) (_hn : 0 < n) (f : ℕ → ℕ)
    (hgrowth : f n < 2 ^ n * f 0) :
    ∃ i < n, f (i + 1) ≤ 2 * f i := by
  by_contra! h
  have hadj : ∀ i < n, 2 * f i < f (i + 1) := by
    intro i hi
    have hnot := h i hi
    omega
  have hgrow : ∀ k ≤ n, 2 ^ k * f 0 ≤ f k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkn : k < n := by omega
        calc
          2 ^ (k + 1) * f 0 = 2 * (2 ^ k * f 0) := by
            rw [pow_succ]
            ring
          _ ≤ 2 * f k := Nat.mul_le_mul_left 2 (ih (by omega))
          _ ≤ f (k + 1) := (hadj k hkn).le
  exact (not_lt_of_ge (hgrow n le_rfl)) hgrowth

/-! ## Exact plateau regularity -/

/-- `B` is plateau-regular at `(rho, eta)` when every dilation at distance at
most `eta` from `rho` has exactly the same finite carrier.  Subtraction is the
truncated subtraction on `ℝ≥0`; applications below always have `eta ≤ rho`. -/
def IsPlateauRegularAt (B : BohrData G) (rho eta : ℝ≥0) : Prop :=
  0 < eta ∧
    ∀ kappa : ℝ≥0, kappa ≤ eta →
      (B.dilate (rho - kappa)).carrier = (B.dilate rho).carrier ∧
      (B.dilate (rho + kappa)).carrier = (B.dilate rho).carrier

/-- The explicit mesh used by the unconditional plateau argument. -/
noncomputable def plateauStep (G : Type*) [Fintype G] : ℝ≥0 :=
  (((2 * (Fintype.card G + 1) : ℕ) : ℝ≥0))⁻¹

private lemma plateauStep_pos : 0 < plateauStep G := by
  simp [plateauStep]

private lemma plateauStep_mul :
    plateauStep G * ((Fintype.card G + 1 : ℕ) : ℝ≥0) = 1 / 2 := by
  rw [plateauStep]
  have hne : (((Fintype.card G + 1 : ℕ) : ℝ≥0)) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_mul]
  exact mul_comm _ _

/-- Every finite Bohr datum has an exactly regular plateau at a scale in
`[1/2,1]`.  The radius is the explicit number
`1 / (4 * (|G| + 1))`.

This is the finite growth/pigeonhole argument in its strongest unconditional
form: among `|G| + 1` adjacent inclusions, two carriers have equal cardinality,
since every carrier is nonempty and has cardinality at most `|G|`. -/
theorem exists_plateauRegularAt (B : BohrData G) :
    ∃ rho eta : ℝ≥0,
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      eta = plateauStep G / 2 ∧
      B.IsPlateauRegularAt rho eta := by
  let step : ℝ≥0 := plateauStep G
  let scale : ℕ → ℝ≥0 := fun i ↦ 1 / 2 + (i : ℝ≥0) * step
  let f : ℕ → ℕ := fun i ↦ (B.dilate (scale i)).carrier.card
  have hf : Monotone f := by
    intro i j hij
    apply Finset.card_le_card
    apply carrier_dilate_mono
    dsimp [scale]
    gcongr
  have hfpos : 1 ≤ f 0 := by
    exact (B.dilate (scale 0)).one_le_card_carrier
  have hfbound : f (Fintype.card G + 1) ≤ Fintype.card G := by
    simpa [f] using Finset.card_le_univ (B.dilate (scale (Fintype.card G + 1))).carrier
  obtain ⟨i, hi, heq⟩ :=
    exists_adjacent_eq_of_bounded (Fintype.card G) f hf hfpos hfbound
  refine ⟨scale i + step / 2, step / 2, ?_, ?_, rfl, ?_⟩
  · dsimp [scale]
    calc
      1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
        le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
      _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
        le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le)
  · have hi' : (i : ℝ≥0) + 1 / 2 ≤ (Fintype.card G + 1 : ℕ) := by
      have hicast : (i : ℝ≥0) ≤ (Fintype.card G : ℕ) := by
        exact_mod_cast hi
      calc
        (i : ℝ≥0) + 1 / 2 ≤ (Fintype.card G : ℕ) + 1 / 2 := by gcongr
        _ ≤ (Fintype.card G + 1 : ℕ) := by
          push_cast
          norm_num
    calc
      scale i + step / 2 =
          1 / 2 + ((i : ℝ≥0) + 1 / 2) * step := by
        simp [scale]
        ring
      _ ≤ 1 / 2 + ((Fintype.card G + 1 : ℕ) : ℝ≥0) * step := by
        gcongr
      _ = 1 := by
        rw [mul_comm, show step = plateauStep G by rfl, plateauStep_mul]
        norm_num
  · refine ⟨by simpa [step] using div_pos plateauStep_pos (by norm_num : (0 : ℝ≥0) < 2), ?_⟩
    intro kappa hkappa
    have hstep : 0 < step := by simpa [step] using (plateauStep_pos (G := G))
    have hkappa_mid : kappa ≤ scale i + step / 2 := by
      exact hkappa.trans (le_add_of_nonneg_left (by positivity))
    have hleft : scale i ≤ scale i + step / 2 - kappa := by
      rw [le_tsub_iff_right hkappa_mid]
      linarith
    have hmidleft : scale i ≤ scale i + step / 2 :=
      le_add_of_nonneg_right (by positivity)
    have hmidright : scale i + step / 2 ≤ scale (i + 1) := by
      dsimp [scale]
      push_cast
      linarith
    have hright : scale i + step / 2 + kappa ≤ scale (i + 1) := by
      dsimp [scale]
      push_cast
      linarith
    have hendsub :
        (B.dilate (scale i)).carrier ⊆ (B.dilate (scale (i + 1))).carrier :=
      carrier_dilate_mono (by
        dsimp [scale]
        push_cast
        nlinarith)
    have hendcard :
        (B.dilate (scale i)).carrier.card =
          (B.dilate (scale (i + 1))).carrier.card := by
      exact heq
    have hendeq :
        (B.dilate (scale i)).carrier =
          (B.dilate (scale (i + 1))).carrier :=
      Finset.eq_of_subset_of_card_le hendsub hendcard.ge
    have all_eq (s : ℝ≥0) (hlo : scale i ≤ s) (hhi : s ≤ scale (i + 1)) :
        (B.dilate s).carrier = (B.dilate (scale i)).carrier := by
      apply Finset.Subset.antisymm
      · have hs := carrier_dilate_mono (B := B) hhi
        rwa [← hendeq] at hs
      · exact carrier_dilate_mono hlo
    constructor
    · exact (all_eq _ hleft ((tsub_le_self.trans hmidright))).trans
        (all_eq _ hmidleft hmidright).symm
    · exact (all_eq _ (hmidleft.trans (le_add_of_nonneg_right (by positivity))) hright).trans
        (all_eq _ hmidleft hmidright).symm

/-! ## A rank-scale coarse regularity interface -/

/-- Coarse regularity on one shell: the outer carrier has cardinality at most
twice that of the inner carrier. -/
def IsCoarselyRegularAt (B : BohrData G) (rho eta : ℝ≥0) : Prop :=
  0 < eta ∧ eta ≤ rho ∧
    (B.dilate (rho + eta)).carrier.card ≤
      2 * (B.dilate (rho - eta)).carrier.card

/-- Standard rank-controlled Bohr regularity.  The harmless `max rank 1`
also covers the rank-zero case.  The constants are deliberately coarse and
fully explicit: for relative perturbations `kappa ≤ 1/(100 d)`, both inner
and outer cardinalities differ from the central one by at most
`100 d kappa` in relative terms. -/
def IsRankRegular (B : BohrData G) : Prop :=
  let d : ℕ := max B.rank 1
  ∀ kappa : ℝ≥0,
    kappa ≤ 1 / (100 * (d : ℝ≥0)) →
      (1 - 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ) ≤
          ((B.dilate (1 - kappa)).carrier.card : ℝ) ∧
      ((B.dilate (1 + kappa)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (kappa : ℝ)) * (B.carrier.card : ℝ)

/-- Rank regularity is stable under a further scalar dilation: this lemma is
only a normalization of the nested-dilation formula. -/
theorem isRankRegular_dilate_iff (B : BohrData G) (rho : ℝ≥0) :
    (B.dilate rho).IsRankRegular ↔
      let d : ℕ := max B.rank 1
      ∀ kappa : ℝ≥0,
        kappa ≤ 1 / (100 * (d : ℝ≥0)) →
          (1 - 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.dilate rho).carrier.card : ℝ) ≤
              ((B.dilate ((1 - kappa) * rho)).carrier.card : ℝ) ∧
          ((B.dilate ((1 + kappa) * rho)).carrier.card : ℝ) ≤
              (1 + 100 * (d : ℝ) * (kappa : ℝ)) *
                ((B.dilate rho).carrier.card : ℝ) := by
  simp [IsRankRegular, mul_comm]

/-- Quantitative regular-value lemma.  If the total growth from scale `1/2`
to scale `1` is less than `2^n`, one of the `n` equal shells has growth at
most two.  Its midpoint lies in `[1/2,1]` and its half-width is exactly
`1/(4n)`. -/
theorem exists_coarselyRegularAt_of_card_growth
    (B : BohrData G) (n : ℕ) (hn : 0 < n)
    (hgrowth :
      (B.dilate 1).carrier.card <
        2 ^ n * (B.dilate (1 / 2)).carrier.card) :
    ∃ rho eta : ℝ≥0,
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      eta = 1 / (4 * (n : ℝ≥0)) ∧
      B.IsCoarselyRegularAt rho eta := by
  let step : ℝ≥0 := 1 / (2 * (n : ℝ≥0))
  let scale : ℕ → ℝ≥0 := fun i ↦ 1 / 2 + (i : ℝ≥0) * step
  let f : ℕ → ℕ := fun i ↦ (B.dilate (scale i)).carrier.card
  have hscale_zero : scale 0 = 1 / 2 := by simp [scale]
  have hscale_n : scale n = 1 := by
    simp [scale, step]
    field_simp
    ring
  have hfgrowth : f n < 2 ^ n * f 0 := by
    simpa [f, hscale_zero, hscale_n] using hgrowth
  obtain ⟨i, hi, hiGrowth⟩ := exists_adjacent_double_le n hn f hfgrowth
  refine ⟨scale i + step / 2, step / 2, ?_, ?_, ?_, ?_⟩
  · dsimp [scale]
    calc
      1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
        le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
      _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
        le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le)
  · have hi_le : (i : ℝ≥0) + 1 / 2 ≤ (n : ℝ≥0) := by
      have hi1 : ((i + 1 : ℕ) : ℝ≥0) ≤ (n : ℝ≥0) := by
        exact_mod_cast (show i + 1 ≤ n by omega)
      calc
        (i : ℝ≥0) + 1 / 2 ≤ (i : ℝ≥0) + 1 := by norm_num
        _ = ((i + 1 : ℕ) : ℝ≥0) := by push_cast; rfl
        _ ≤ (n : ℝ≥0) := hi1
    calc
      scale i + step / 2 = 1 / 2 + ((i : ℝ≥0) + 1 / 2) * step := by
        simp [scale]
        ring
      _ ≤ 1 / 2 + (n : ℝ≥0) * step := by gcongr
      _ = 1 := by
        simp [step]
        field_simp
        ring
  · simp [step]
    ring
  · refine ⟨by positivity, ?_, ?_⟩
    · have : step / 2 ≤ 1 / 2 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 2)]
        dsimp [step]
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 2 * n by omega)
        · have hnreal : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
          positivity
      exact this.trans (by
        dsimp [scale]
        calc
          1 / 2 ≤ 1 / 2 + (i : ℝ≥0) * step :=
            le_add_of_nonneg_right (show 0 ≤ (i : ℝ≥0) * step by exact bot_le)
          _ ≤ 1 / 2 + (i : ℝ≥0) * step + step / 2 :=
            le_add_of_nonneg_right (show 0 ≤ step / 2 by exact bot_le))
    · have hminus : scale i + step / 2 - step / 2 = scale i := by
        exact add_tsub_cancel_right _ _
      have hplus : scale i + step / 2 + step / 2 = scale (i + 1) := by
        dsimp [scale]
        push_cast
        ring
      simpa [hminus, hplus, f] using hiGrowth

/-! ## Translation and normalized-indicator consequences -/

/-- Translation of a finite set by addition on the right. -/
noncomputable def translateFinset (A : Finset G) (t : G) : Finset G :=
  A.map (Equiv.addRight t).toEmbedding

@[simp] lemma mem_translateFinset {A : Finset G} {t x : G} :
    x ∈ translateFinset A t ↔ x - t ∈ A := by
  simp [translateFinset, sub_eq_add_neg]

@[simp] lemma card_translateFinset (A : Finset G) (t : G) :
    (translateFinset A t).card = A.card := by
  simp [translateFinset]

/-- A small translate and the central carrier can differ only in the shell
between the inner and outer dilates.  This is the set-theoretic heart of the
usual Bohr normalized-indicator translation estimate. -/
theorem symmDiff_translate_carrier_subset_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    (translateFinset (B.dilate rho).carrier t) ∆ (B.dilate rho).carrier ⊆
      (B.dilate (rho + eta)).carrier \ (B.dilate (rho - eta)).carrier := by
  intro x hx
  rw [Finset.mem_symmDiff] at hx
  rw [Finset.mem_sdiff]
  constructor
  · rcases hx with hx | hx
    · rw [mem_translateFinset] at hx
      have hxt := add_mem_dilate hx.1 ht
      simpa using hxt
    · exact carrier_dilate_mono (le_add_of_nonneg_right (by positivity)) hx.1
  · intro hinner
    have hinner_center : x ∈ (B.dilate rho).carrier := by
      exact carrier_dilate_mono (tsub_le_self) hinner
    have hinner_shift : x - t ∈ (B.dilate rho).carrier := by
      have hneg : -t ∈ (B.dilate eta).carrier := neg_mem_carrier.mpr ht
      have hadd := add_mem_dilate hinner hneg
      simpa [sub_eq_add_neg, tsub_add_cancel_of_le heta] using hadd
    have hinner_translate : x ∈ translateFinset (B.dilate rho).carrier t := by
      rwa [mem_translateFinset]
    rcases hx with hx | hx
    · exact hx.2 hinner_center
    · exact hx.2 hinner_translate

/-- Cardinal form of `symmDiff_translate_carrier_subset_shell`. -/
theorem card_symmDiff_translate_carrier_le_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ((translateFinset (B.dilate rho).carrier t) ∆
        (B.dilate rho).carrier).card ≤
      (B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card := by
  have hinner_outer :
      (B.dilate (rho - eta)).carrier ⊆
        (B.dilate (rho + eta)).carrier :=
    carrier_dilate_mono ((tsub_le_self).trans (le_add_of_nonneg_right (by positivity)))
  calc
    ((translateFinset (B.dilate rho).carrier t) ∆
        (B.dilate rho).carrier).card ≤
        ((B.dilate (rho + eta)).carrier \
          (B.dilate (rho - eta)).carrier).card :=
      Finset.card_le_card (symmDiff_translate_carrier_subset_shell heta ht)
    _ = (B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card :=
      Finset.card_sdiff_of_subset hinner_outer

/-- The counting-measure `L^1` distance of two normalized indicators is the
relative cardinality of their symmetric difference.  Here the two finite sets
have equal cardinality because one is a translate of the other. -/
theorem sum_abs_normalizedIndicator_translate_eq_card_symmDiff
    (A : Finset G) (t : G) :
    ∑ x : G, |normalizedIndicator A (x - t) - normalizedIndicator A x| =
      (((translateFinset A t) ∆ A).card : ℝ) / (A.card : ℝ) := by
  have hpoint (x : G) :
      |normalizedIndicator A (x - t) - normalizedIndicator A x| =
        if x ∈ (translateFinset A t) ∆ A then (A.card : ℝ)⁻¹ else 0 := by
    by_cases hxt : x - t ∈ A <;> by_cases hx : x ∈ A <;>
      simp [normalizedIndicator, Finset.mem_symmDiff, mem_translateFinset,
        hxt, hx, abs_of_nonneg]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

/-- The standard normalized-indicator translation estimate in shell form. -/
theorem sum_abs_normalizedIndicator_translate_le_shell
    {B : BohrData G} {rho eta : ℝ≥0} (heta : eta ≤ rho) {t : G}
    (ht : t ∈ (B.dilate eta).carrier) :
    ∑ x : G,
        |normalizedIndicator (B.dilate rho).carrier (x - t) -
          normalizedIndicator (B.dilate rho).carrier x| ≤
      (((B.dilate (rho + eta)).carrier.card -
        (B.dilate (rho - eta)).carrier.card : ℕ) : ℝ) /
          ((B.dilate rho).carrier.card : ℝ) := by
  rw [sum_abs_normalizedIndicator_translate_eq_card_symmDiff]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  gcongr
  exact_mod_cast card_symmDiff_translate_carrier_le_shell heta ht

/-- The standard `O(rank * kappa)` normalized-indicator translation estimate
for a rank-regular Bohr carrier. -/
theorem sum_abs_normalizedIndicator_translate_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    ∑ x : G,
        |normalizedIndicator B.carrier (x - t) -
          normalizedIndicator B.carrier x| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
  let d : ℕ := max B.rank 1
  have hd : 0 < d := by simp [d]
  have hkappa' : kappa ≤ 1 / (100 * (d : ℝ≥0)) := by
    simpa [d] using hkappa
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa'.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hshell :=
    sum_abs_normalizedIndicator_translate_le_shell
      (B := B) (rho := (1 : ℝ≥0)) (eta := kappa) hkappa_one ht
  simp only [dilate_one] at hshell
  simp only [IsRankRegular] at hreg
  have hcards := hreg kappa (by simpa [d] using hkappa')
  have hinner_outer :
      (B.dilate (1 - kappa)).carrier.card ≤
        (B.dilate (1 + kappa)).carrier.card :=
    Finset.card_le_card
      (carrier_dilate_mono
        (tsub_le_self.trans (le_add_of_nonneg_right (show 0 ≤ kappa by exact bot_le))))
  have hcenter_pos : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  apply hshell.trans
  rw [Nat.cast_sub hinner_outer]
  rw [div_le_iff₀ hcenter_pos]
  nlinarith [hcards.1, hcards.2]

end BohrData

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BohrEstimates.lean` -/

section
/-!
# Elementary estimates on regular finite Bohr sets

This file proves the three normalization-sensitive Bohr estimates used in the
Kelley--Meka density-increment argument.

* On an exact regular plateau, convolution by a nonnegative measure supported
  on the small Bohr carrier does not move the normalized carrier measure.  In
  particular the corresponding counting-measure `L¹` error is zero (and hence
  is stronger than the usual `O (rho * rank)` estimate).
* Coarse regularity of one shell gives the pointwise factor-two Bohr
  majorization inequality.
* Exact plateau invariance gives a two-scale Bourgain narrowing alternative.

All convolutions and indicators below use counting-measure probability
normalization from `FiniteConvolution.lean`; consequently there are no hidden
factors of `|G|`.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Translation invariance and convolution -/

/-- The standard rank-linear regular-Bohr convolution estimate, with the
fully explicit constant inherited from `RegularBohr.lean`. -/
theorem sum_abs_normalizedConvolution_error_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (ν : G → ℝ) (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier) :
    ∑ x : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) * ∑ t : G, ν t := by
  let E : ℝ := 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hpoint (x : G) :
      |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
        ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
    rw [normalizedConvolution_comm]
    simp only [normalizedConvolution]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ t : G, ν t *
          (normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x)| ≤
          ∑ t : G, |ν t *
            (normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x)| :=
        abs_sum_le_sum_abs _ _
      _ = ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
        apply Finset.sum_congr rfl
        intro t _
        rw [abs_mul, abs_of_nonneg (hνnonneg t)]
  calc
    ∑ x : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν x -
          (∑ t : G, ν t) * normalizedIndicator B.carrier x| ≤
        ∑ x : G, ∑ t : G, ν t *
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
      exact Finset.sum_le_sum fun x _ ↦ hpoint x
    _ = ∑ t : G, ν t * ∑ x : G,
          |normalizedIndicator B.carrier (x - t) - normalizedIndicator B.carrier x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
    _ ≤ ∑ t : G, ν t * E := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : ν t = 0
      · simp [ht]
      · exact mul_le_mul_of_nonneg_left
          (BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
            hreg hκ (hνsupp t ht)) (hνnonneg t)
    _ = (∑ t : G, ν t) * E := by rw [Finset.sum_mul]
    _ = E * ∑ t : G, ν t := by ring
    _ = 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) * ∑ t : G, ν t := rfl

/-! ## Bohr majorization -/

/-- A coarsely regular shell majorizes its central Bohr measure after
smoothing by any probability measure supported on the small carrier.

The factor `2` is exactly the factor in `IsCoarselyRegularAt`; no asymptotic
notation is used. -/
theorem normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
    {B : BohrData G} {rho eta : ℝ≥0}
    (hreg : B.IsCoarselyRegularAt rho eta)
    (ν : G → ℝ)
    (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνmass : ∑ t : G, ν t = 1)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate eta).carrier)
    (x : G) :
    normalizedIndicator (B.dilate rho).carrier x ≤
      2 * normalizedConvolution
        (normalizedIndicator (B.dilate (rho + eta)).carrier) ν x := by
  let Kminus := (B.dilate (rho - eta)).carrier
  let K := (B.dilate rho).carrier
  let Kplus := (B.dilate (rho + eta)).carrier
  have hinner : Kminus.card ≤ K.card := by
    apply Finset.card_le_card
    exact BohrData.carrier_dilate_mono (tsub_le_self : rho - eta ≤ rho)
  have hcard : Kplus.card ≤ 2 * K.card :=
    hreg.2.2.trans (Nat.mul_le_mul_left 2 hinner)
  have hKpos : (0 : ℝ) < K.card := by
    exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
  have hKpluspos : (0 : ℝ) < Kplus.card := by
    exact_mod_cast (B.dilate (rho + eta)).carrier_nonempty.card_pos
  have hconv (hx : x ∈ K) :
      normalizedConvolution (normalizedIndicator Kplus) ν x =
        (Kplus.card : ℝ)⁻¹ := by
    rw [normalizedConvolution_comm]
    simp only [normalizedConvolution]
    calc
      ∑ t : G, ν t * normalizedIndicator Kplus (x - t) =
          ∑ t : G, ν t * (Kplus.card : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro t _
        by_cases ht : ν t = 0
        · simp [ht]
        · have hxt : x - t ∈ Kplus :=
            BohrData.sub_mem_dilate hx (hνsupp t ht)
          rw [normalizedIndicator_apply_mem hxt]
      _ = (∑ t : G, ν t) * (Kplus.card : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
      _ = (Kplus.card : ℝ)⁻¹ := by rw [hνmass, one_mul]
  by_cases hx : x ∈ K
  · rw [show (B.dilate rho).carrier = K by rfl,
      normalizedIndicator_apply_mem hx, hconv hx]
    calc
      (K.card : ℝ)⁻¹ = 1 / (K.card : ℝ) := by rw [one_div]
      _ ≤ 2 / (Kplus.card : ℝ) := by
        rw [div_le_div_iff₀ hKpos hKpluspos]
        simpa only [one_mul] using (show (Kplus.card : ℝ) ≤ 2 * K.card by
          exact_mod_cast hcard)
      _ = 2 * (Kplus.card : ℝ)⁻¹ := by rw [div_eq_mul_inv]
  · rw [show (B.dilate rho).carrier = K by rfl,
      normalizedIndicator_apply_not_mem hx]
    exact mul_nonneg (by norm_num)
      (normalizedConvolution_nonneg
        (normalizedIndicator_nonneg Kplus) hνnonneg x)

/-- Rank-regular specialization of Bohr majorization.  The explicit
`1/(400 d)` scale ensures the outer shell is at most twice the inner shell,
so the preceding factor-two estimate applies. -/
theorem normalizedIndicator_le_two_mul_convolution_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0} (hκpos : 0 < κ)
    (hκ : κ ≤ 1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (ν : G → ℝ) (hνnonneg : ∀ t, 0 ≤ ν t)
    (hνmass : ∑ t : G, ν t = 1)
    (hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier)
    (x : G) :
    normalizedIndicator B.carrier x ≤
      2 * normalizedConvolution
        (normalizedIndicator (B.dilate (1 + κ)).carrier) ν x := by
  let d : ℕ := max B.rank 1
  have hd : 0 < d := by simp [d]
  have hκd : κ ≤ 1 / (400 * (d : ℝ≥0)) := by simpa [d] using hκ
  have hκreg : κ ≤ 1 / (100 * (d : ℝ≥0)) := by
    apply hκd.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num : (100 : ℝ≥0) ≤ 400) (by positivity)
  have hκone : κ ≤ 1 := by
    apply hκreg.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hcards := hreg κ (by simpa [d] using hκreg)
  have hquarter : (100 : ℝ) * d * (κ : ℝ) ≤ 1 / 4 := by
    have hκreal : (κ : ℝ) ≤ 1 / (400 * (d : ℝ)) := by
      exact_mod_cast hκd
    have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
    calc
      (100 : ℝ) * d * (κ : ℝ) ≤ 100 * d * (1 / (400 * (d : ℝ))) := by gcongr
      _ = 1 / 4 := by field_simp; ring
  have hcardreal :
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
        2 * ((B.dilate (1 - κ)).carrier.card : ℝ) := by
    nlinarith [hcards.1, hcards.2,
      show (0 : ℝ) < B.carrier.card by exact_mod_cast B.carrier_nonempty.card_pos]
  have hcard :
      (B.dilate (1 + κ)).carrier.card ≤
        2 * (B.dilate (1 - κ)).carrier.card := by
    exact_mod_cast hcardreal
  have hcoarse : B.IsCoarselyRegularAt 1 κ := ⟨hκpos, hκone, hcard⟩
  simpa only [BohrData.dilate_one] using
    normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
      hcoarse ν hνnonneg hνmass hνsupp x

/-! ## A finite two-scale narrowing alternative -/

/-- The `{0,1}`-valued indicator used for local relative densities. -/
def finsetIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then 1 else 0

@[simp] theorem finsetIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    finsetIndicator A x = 1 := by simp [finsetIndicator, hx]

@[simp] theorem finsetIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    finsetIndicator A x = 0 := by simp [finsetIndicator, hx]

/-- Relative density of `A` in a nonempty ambient finite set. -/
def relativeDensityOn (A K : Finset G) : ℝ :=
  (A.card : ℝ) / K.card

/-- The density of `A` on the translate `x - C`, normalized by `|C|`. -/
def localDensity (A C : Finset G) (x : G) : ℝ :=
  normalizedConvolution (finsetIndicator A) (normalizedIndicator C) x

/-- Pairing a subset indicator with the probability measure of its ambient
set gives the relative density. -/
theorem sum_finsetIndicator_mul_normalizedIndicator
    {A K : Finset G} (hAK : A ⊆ K) (hK : K.Nonempty) :
    ∑ x : G, finsetIndicator A x * normalizedIndicator K x =
      relativeDensityOn A K := by
  have hsum :
      ∑ x ∈ A, finsetIndicator A x * normalizedIndicator K x =
        ∑ x : G, finsetIndicator A x * normalizedIndicator K x := by
    apply Finset.sum_subset (Finset.subset_univ A)
    intro x _ hxA
    simp [finsetIndicator, hxA]
  rw [← hsum]
  calc
    ∑ x ∈ A, finsetIndicator A x * normalizedIndicator K x =
        ∑ _x ∈ A, (K.card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [finsetIndicator_apply_mem hx,
        normalizedIndicator_apply_mem (hAK hx), one_mul]
    _ = relativeDensityOn A K := by
      simp [relativeDensityOn, div_eq_mul_inv, hK.card_ne_zero]

/-- The normalized average of a local-density function differs from the
ambient relative density only by the regular-Bohr boundary error. -/
theorem abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {A C : Finset G} (hAK : A ⊆ B.carrier) (hC : C.Nonempty)
    (hCsmall : C ⊆ (B.dilate κ).carrier) :
    |(∑ x : G, normalizedIndicator B.carrier x * localDensity A C x) -
        relativeDensityOn A B.carrier| ≤
      200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
  let ν : G → ℝ := fun t ↦ normalizedIndicator C (-t)
  have hνnonneg : ∀ t, 0 ≤ ν t := fun t ↦ normalizedIndicator_nonneg C (-t)
  have hνmass : ∑ t : G, ν t = 1 := by
    calc
      ∑ t : G, ν t = ∑ t : G, normalizedIndicator C t := by
        exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun _ ↦ rfl)
      _ = 1 := sum_normalizedIndicator hC
  have hνsupp : ∀ t, ν t ≠ 0 → t ∈ (B.dilate κ).carrier := by
    intro t ht
    have hneg : -t ∈ C := (normalizedIndicator_ne_zero_iff hC (-t)).mp ht
    exact BohrData.neg_mem_carrier.mp (hCsmall hneg)
  have hconv :
      ∑ y : G,
          |normalizedConvolution (normalizedIndicator B.carrier) ν y -
            normalizedIndicator B.carrier y| ≤
        200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
    simpa [hνmass] using
      sum_abs_normalizedConvolution_error_le_of_rankRegular
        hreg hκ ν hνnonneg hνsupp
  have havg :
      ∑ x : G, normalizedIndicator B.carrier x * localDensity A C x =
        ∑ y : G, finsetIndicator A y *
          normalizedConvolution (normalizedIndicator B.carrier) ν y := by
    simp only [localDensity, normalizedConvolution, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ν]
    rw [neg_sub]
    ring
  have hbase :
      ∑ y : G, finsetIndicator A y * normalizedIndicator B.carrier y =
        relativeDensityOn A B.carrier :=
    sum_finsetIndicator_mul_normalizedIndicator hAK B.carrier_nonempty
  rw [havg, ← hbase, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ y : G, finsetIndicator A y *
        (normalizedConvolution (normalizedIndicator B.carrier) ν y -
          normalizedIndicator B.carrier y)| ≤
        ∑ y : G, |finsetIndicator A y *
          (normalizedConvolution (normalizedIndicator B.carrier) ν y -
            normalizedIndicator B.carrier y)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : G,
        |normalizedConvolution (normalizedIndicator B.carrier) ν y -
          normalizedIndicator B.carrier y| := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ A <;> simp [finsetIndicator, hy]
    _ ≤ 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := hconv

/-- The quantitative rank-regular Bourgain narrowing alternative.  The last
hypothesis is the explicit version of `kappa ≪ alpha * epsilon / rank`; with
the constants in this development it absorbs both boundary errors. -/
theorem bohr_narrowing_alternative_of_rankRegular
    {B : BohrData G} (hreg : B.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {A C₁ C₂ : Finset G}
    (hA : A.Nonempty) (hAK : A ⊆ B.carrier)
    (hC₁ : C₁.Nonempty) (hC₂ : C₂.Nonempty)
    (hC₁small : C₁ ⊆ (B.dilate κ).carrier)
    (hC₂small : C₂ ⊆ (B.dilate κ).carrier)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall :
      400 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) ≤
        ε * relativeDensityOn A B.carrier / 4) :
    (∃ x ∈ B.carrier,
        (1 - ε) * relativeDensityOn A B.carrier ≤ localDensity A C₁ x ∧
        (1 - ε) * relativeDensityOn A B.carrier ≤ localDensity A C₂ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A B.carrier ≤ localDensity A C₁ x) ∨
      (∃ x : G,
        (1 + ε / 2) * relativeDensityOn A B.carrier ≤ localDensity A C₂ x) := by
  let K := B.carrier
  let α : ℝ := relativeDensityOn A K
  let E : ℝ := 200 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  let M₁ : ℝ := ∑ x : G, normalizedIndicator K x * localDensity A C₁ x
  let M₂ : ℝ := ∑ x : G, normalizedIndicator K x * localDensity A C₂ x
  have hK : K.Nonempty := B.carrier_nonempty
  have hα : 0 < α := by
    dsimp [α, K, relativeDensityOn]
    exact div_pos (by exact_mod_cast hA.card_pos) (by exact_mod_cast hK.card_pos)
  have havg₁ : |M₁ - α| ≤ E := by
    simpa [M₁, α, E, K] using
      abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
        hreg hκ hAK hC₁ hC₁small
  have havg₂ : |M₂ - α| ≤ E := by
    simpa [M₂, α, E, K] using
      abs_sum_normalizedIndicator_mul_localDensity_sub_le_of_rankRegular
        hreg hκ hAK hC₂ hC₂small
  have hM₁ : α - E ≤ M₁ := by
    have := (abs_le.mp havg₁).1
    linarith
  have hM₂ : α - E ≤ M₂ := by
    have := (abs_le.mp havg₂).1
    linarith
  have hsmallE : 2 * E ≤ ε * α / 4 := by
    calc
      2 * E = 400 * ((max B.rank 1 : ℕ) : ℝ) * (κ : ℝ) := by
        dsimp [E]
        ring
      _ ≤ ε * relativeDensityOn A B.carrier / 4 := hsmall
      _ = ε * α / 4 := by rfl
  by_cases hgood :
      ∃ x ∈ K,
        (1 - ε) * α ≤ localDensity A C₁ x ∧
        (1 - ε) * α ≤ localDensity A C₂ x
  · exact Or.inl hgood
  by_cases hinc₁ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₁ x
  · exact Or.inr (Or.inl hinc₁)
  by_cases hinc₂ : ∃ x : G, (1 + ε / 2) * α ≤ localDensity A C₂ x
  · exact Or.inr (Or.inr hinc₂)
  exfalso
  let T : ℝ := 2 * α - ε * α / 2
  have hpoint : ∀ x ∈ K,
      localDensity A C₁ x + localDensity A C₂ x < T := by
    intro x hx
    have hu₁ : localDensity A C₁ x < (1 + ε / 2) * α :=
      lt_of_not_ge (fun h ↦ hinc₁ ⟨x, h⟩)
    have hu₂ : localDensity A C₂ x < (1 + ε / 2) * α :=
      lt_of_not_ge (fun h ↦ hinc₂ ⟨x, h⟩)
    have hlow :
        localDensity A C₁ x < (1 - ε) * α ∨
          localDensity A C₂ x < (1 - ε) * α := by
      by_cases h₁ : (1 - ε) * α ≤ localDensity A C₁ x
      · right
        exact lt_of_not_ge (fun h₂ ↦ hgood ⟨x, hx, h₁, h₂⟩)
      · left
        exact lt_of_not_ge h₁
    rcases hlow with hlow₁ | hlow₂
    · dsimp [T]
      nlinarith
    · dsimp [T]
      nlinarith
  have hweighted :
      ∑ x : G, normalizedIndicator K x *
          (localDensity A C₁ x + localDensity A C₂ x) <
        ∑ x : G, normalizedIndicator K x * T := by
    apply Finset.sum_lt_sum
    · intro x _
      by_cases hx : x ∈ K
      · exact mul_le_mul_of_nonneg_left (hpoint x hx).le
          (normalizedIndicator_nonneg K x)
      · simp [normalizedIndicator_apply_not_mem hx]
    · refine ⟨0, Finset.mem_univ 0, ?_⟩
      have hz : 0 ∈ K := B.zero_mem_carrier
      exact mul_lt_mul_of_pos_left (hpoint 0 hz)
        ((normalizedIndicator_pos_iff hK 0).2 hz)
  have hweighted' : M₁ + M₂ < T := by
    calc
      M₁ + M₂ = ∑ x : G, normalizedIndicator K x *
          (localDensity A C₁ x + localDensity A C₂ x) := by
        dsimp [M₁, M₂]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ < ∑ x : G, normalizedIndicator K x * T := hweighted
      _ = (∑ x : G, normalizedIndicator K x) * T := by rw [Finset.sum_mul]
      _ = T := by rw [sum_normalizedIndicator hK, one_mul]
  dsimp [T] at hweighted'
  nlinarith

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BourgainRegular.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Bourgain regular dilates of finite Bohr sets

The first part of this file proves the rank-only relative-volume estimate

`|B_1| ≤ 4^rank(B) |B_{1/2}|`.

The proof is the finite torus-box argument.  We choose the representative of
each circle coordinate in `[-1/2,1/2)`, split the interval allowed by a Bohr
constraint into four cells, and inject every signature fiber into `B_{1/2}`
by subtracting a fixed member of the fiber.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Canonical representatives and four-cell coding -/

/-- The canonical representative of a point of `ℝ / ℤ` in `[-1/2,1/2)`. -/
def circleRep (z : AddCircle (1 : ℝ)) : ℝ :=
  (QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2) z).1

lemma circleRep_mem (z : AddCircle (1 : ℝ)) :
    circleRep z ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2) := by
  let e := QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2)
  change -1 / 2 ≤ circleRep z ∧ circleRep z < 1 / 2
  constructor
  · exact (e z).2.1
  · have hz := (e z).2.2
    norm_num at hz ⊢
    exact hz

@[simp] lemma circleRep_coe (z : AddCircle (1 : ℝ)) :
    ((circleRep z : ℝ) : AddCircle (1 : ℝ)) = z := by
  let e := QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num) (-1 / 2)
  have h := e.symm_apply_apply z
  change ((circleRep z : ℝ) : AddCircle (1 : ℝ)) = z
  simpa only [e, circleRep, QuotientAddGroup.equivIcoMod_symm_apply] using h

lemma abs_circleRep_le_half (z : AddCircle (1 : ℝ)) : |circleRep z| ≤ 1 / 2 := by
  have hz := circleRep_mem z
  rw [Set.mem_Ico] at hz
  rw [abs_le]
  constructor <;> linarith

lemma norm_eq_abs_circleRep (z : AddCircle (1 : ℝ)) : ‖z‖ = |circleRep z| := by
  calc
    ‖z‖ = ‖((circleRep z : ℝ) : AddCircle (1 : ℝ))‖ := by rw [circleRep_coe]
    _ = |circleRep z| :=
      (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2
        (by simpa using abs_circleRep_le_half z)

lemma norm_sub_le_abs_circleRep_sub (z w : AddCircle (1 : ℝ)) :
    ‖z - w‖ ≤ |circleRep z - circleRep w| := by
  have hcoe :
      (((circleRep z - circleRep w : ℝ) : ℝ) : AddCircle (1 : ℝ)) = z - w := by
    simp
  rw [← hcoe]
  simpa only [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : ℝ)) :
        ‖((circleRep z - circleRep w : ℝ) : AddCircle (1 : ℝ))‖ ≤
          ‖circleRep z - circleRep w‖)

/-- Four consecutive cells in `[-w,w]`, each of diameter at most `w/2`.
The definition is total; its diameter property is used only for nonnegative
`w` and inputs in `[-w,w]`. -/
def fourCell (w r : ℝ) : Fin 4 :=
  if r < -(w / 2) then 0
  else if r < 0 then 1
  else if r < w / 2 then 2
  else 3

lemma abs_sub_le_half_of_fourCell_eq {w r s : ℝ}
    (hw : 0 ≤ w) (hr : |r| ≤ w) (hs : |s| ≤ w)
    (hcell : fourCell w r = fourCell w s) :
    |r - s| ≤ w / 2 := by
  rw [abs_le] at hr hs ⊢
  unfold fourCell at hcell
  split_ifs at hcell
  all_goals try { omega }
  all_goals constructor <;> linarith

/-- The four-cell signature of a point in the unit dilate. -/
def unitSignature (B : BohrData G) (x : ↥(B.dilate 1).carrier) :
    B.freq → Fin 4 :=
  fun γ ↦ fourCell (B.width γ.1 : ℝ) (circleRep (γ.1 x.1))

private lemma sub_mem_half_of_unitSignature_eq (B : BohrData G)
    {x y : ↥(B.dilate 1).carrier}
    (hxy : B.unitSignature x = B.unitSignature y) :
    x.1 - y.1 ∈ (B.dilate (1 / 2)).carrier := by
  rw [mem_carrier]
  intro γ hγ
  have hx := (mem_carrier (B.dilate 1) x.1).mp x.2 γ hγ
  have hy := (mem_carrier (B.dilate 1) y.1).mp y.2 γ hγ
  simp only [width_dilate, one_mul, NNReal.coe_one, NNReal.coe_mul] at hx hy ⊢
  rw [map_sub]
  have hxrep : |circleRep (γ x.1)| ≤ (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hyrep : |circleRep (γ y.1)| ≤ (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hcoord := congrFun hxy ⟨γ, hγ⟩
  calc
    ‖γ x.1 - γ y.1‖ ≤ |circleRep (γ x.1) - circleRep (γ y.1)| :=
      norm_sub_le_abs_circleRep_sub _ _
    _ ≤ (B.width γ : ℝ) / 2 :=
      abs_sub_le_half_of_fourCell_eq (by positivity) hxrep hyrep hcoord
    _ = ((1 / 2 : NNReal) : ℝ) * (B.width γ : ℝ) := by
      norm_num
      ring

private lemma card_unitSignature_fiber_le (B : BohrData G)
    (a : B.freq → Fin 4) :
    Fintype.card {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} ≤
      (B.dilate (1 / 2)).carrier.card := by
  classical
  by_cases hfiber : Nonempty
      {x : ↥(B.dilate 1).carrier // B.unitSignature x = a}
  · let x₀ : {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} :=
      Classical.choice hfiber
    let f : {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} →
        ↥(B.dilate (1 / 2)).carrier :=
      fun x ↦ ⟨x.1.1 - x₀.1.1, sub_mem_half_of_unitSignature_eq B
        (x.2.trans x₀.2.symm)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congr_arg (fun z ↦ z.1) hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card {x : ↥(B.dilate 1).carrier // B.unitSignature x = a} ≤
          Fintype.card ↥(B.dilate (1 / 2)).carrier :=
        Fintype.card_le_of_injective f hf
      _ = (B.dilate (1 / 2)).carrier.card := Fintype.card_coe _
  · simp only [not_nonempty_iff] at hfiber
    simp

/-- Rank-only relative volume growth between the half and unit dilates. -/
theorem card_unit_le_four_pow_rank_mul_card_half (B : BohrData G) :
    (B.dilate 1).carrier.card ≤
      4 ^ B.rank * (B.dilate (1 / 2)).carrier.card := by
  classical
  let S := B.freq → Fin 4
  let q : ↥(B.dilate 1).carrier → S := B.unitSignature
  have hfiber : ∀ a : S,
      Fintype.card {x : ↥(B.dilate 1).carrier // q x = a} ≤
        (B.dilate (1 / 2)).carrier.card := by
    intro a
    exact card_unitSignature_fiber_le B a
  have hcardS : Fintype.card S = 4 ^ B.rank := by
    dsimp [S, rank]
    rw [Fintype.card_pi]
    simp
  rw [← Fintype.card_coe (B.dilate 1).carrier, ← hcardS]
  by_contra h
  have hlt :
      Fintype.card S * (B.dilate (1 / 2)).carrier.card <
        Fintype.card ↥(B.dilate 1).carrier := by omega
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤ (B.dilate (1 / 2)).carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- A buffered version of the relative-volume estimate.  It is convenient in
the regular-value argument because every permitted perturbation of a scale in
`[1/2,1]` remains between `1/4` and `2`. -/
theorem card_two_le_four_pow_three_rank_mul_card_quarter (B : BohrData G) :
    (B.dilate 2).carrier.card ≤
      4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
  have h₂ := card_unit_le_four_pow_rank_mul_card_half (B.dilate 2)
  have h₁ := card_unit_le_four_pow_rank_mul_card_half B
  have hhalf := card_unit_le_four_pow_rank_mul_card_half (B.dilate (1 / 2))
  simp only [rank_dilate, dilate_dilate, mul_one] at h₂ hhalf
  norm_num at h₂ hhalf
  calc
    (B.dilate 2).carrier.card ≤ 4 ^ B.rank * B.carrier.card := h₂
    _ ≤ 4 ^ B.rank * (4 ^ B.rank * (B.dilate (1 / 2)).carrier.card) := by
      gcongr
      simpa using h₁
    _ ≤ 4 ^ B.rank *
        (4 ^ B.rank * (4 ^ B.rank * (B.dilate (1 / 4)).carrier.card)) := by
      gcongr
    _ = 4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
      rw [← mul_assoc, ← pow_add, ← mul_assoc, ← pow_add]
      congr 2
      omega

/-! ## The one-dimensional regular-value lemma -/

/-- A monotone function whose total growth on a buffered interval is less
than `5` has a point in `[1/2,1]` at which every secant contained in the
buffer has slope at most `60`.

This is Bourgain's finite-growth argument.  If every point were bad, attach
to it a bad secant interval.  Vitali selects disjoint intervals whose
six-fold open enlargements cover `[1/2,1]`.  Hence their total length is at
least `1/12`; badness makes the sum of the corresponding increments greater
than `5`, while disjointness and monotonicity telescope that sum below the
total growth. -/
private theorem exists_regular_point_of_monotone
    (f : ℝ → ℝ) (hf : Monotone f)
    (hgrowth : f (5 / 4) - f (1 / 4) < 5) :
    ∃ x ∈ Set.Icc (1 / 2 : ℝ) 1,
      ∀ y ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
        |f y - f x| ≤ 60 * |y - x| := by
  classical
  by_contra! hregular
  let Bad : Set (ℝ × ℝ) := {p |
    1 / 4 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 5 / 4 ∧
      60 * (p.2 - p.1) < f p.2 - f p.1}
  let center : (ℝ × ℝ) → ℝ := fun p ↦ (p.1 + p.2) / 2
  let radius : (ℝ × ℝ) → ℝ := fun p ↦ (p.2 - p.1) / 2
  have hradius_pos {p : ℝ × ℝ} (hp : p ∈ Bad) : 0 < radius p := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  have hradius_le (p : ℝ × ℝ) (hp : p ∈ Bad) : radius p ≤ 1 / 2 := by
    dsimp [Bad] at hp
    dsimp [radius]
    linarith
  obtain ⟨u, huBad, huDisjoint, huCover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      Bad center radius (1 / 2) hradius_le 5 (by norm_num)
  have hcentralCover : Set.Icc (1 / 2 : ℝ) 1 ⊆
      ⋃ b : ↥u, Metric.ball (center b.1) (6 * radius b.1) := by
    intro x hx
    obtain ⟨y, hybuf, hxy⟩ := hregular x hx
    let p : ℝ × ℝ := (min x y, max x y)
    have hpbuf : p ∈ Bad := by
      dsimp [Bad, p]
      have hxbuf : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
        constructor <;> linarith [hx.1, hx.2]
      rcases le_total x y with hle | hle
      · simp only [min_eq_left hle, max_eq_right hle]
        have habs : |f y - f x| = f y - f x :=
          abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hxbuf.1, lt_of_not_ge (fun heq ↦ by
          have : y = x := le_antisymm heq hle
          subst y
          norm_num at hxy), hybuf.2, hxy⟩
      · simp only [min_eq_right hle, max_eq_left hle]
        have habs : |f y - f x| = f x - f y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (hf hle))
        have hdist : |y - x| = x - y := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hle)
        rw [habs, hdist] at hxy
        exact ⟨hybuf.1, lt_of_not_ge (fun heq ↦ by
          have : x = y := le_antisymm heq hle
          subst y
          norm_num at hxy), hxbuf.2, hxy⟩
    obtain ⟨b, hbu, hsub⟩ := huCover p hpbuf
    have hxp : x ∈ Metric.closedBall (center p) (radius p) := by
      rw [Real.closedBall_eq_Icc]
      dsimp [center, radius, p]
      constructor <;> rcases le_total x y with hle | hle <;>
        simp [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hle] <;> linarith
    have hxb : x ∈ Metric.closedBall (center b) (5 * radius b) := hsub hxp
    rw [Metric.mem_closedBall] at hxb
    rw [Set.mem_iUnion]
    refine ⟨⟨b, hbu⟩, ?_⟩
    rw [Metric.mem_ball]
    have hbr : 0 < radius b := hradius_pos (huBad hbu)
    linarith
  obtain ⟨v, hvCover⟩ := isCompact_Icc.elim_finite_subcover
    (fun b : ↥u ↦ Metric.ball (center b.1) (6 * radius b.1))
    (fun _ ↦ Metric.isOpen_ball) hcentralCover
  have hv_nonempty : v.Nonempty := by
    by_contra hv
    rw [Finset.not_nonempty_iff_eq_empty] at hv
    simpa [hv] using hvCover (show (1 / 2 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num)
  have hvolume : (1 / 2 : ℝ) ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
    have hm : MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
        MeasureTheory.volume (⋃ b ∈ v,
          Metric.ball (center b.1) (6 * radius b.1)) :=
      MeasureTheory.measure_mono hvCover
    have hright : 0 ≤ 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro b hb
      have := hradius_pos (huBad b.2)
      dsimp [radius] at this
      linarith
    rw [← ENNReal.ofReal_le_ofReal_iff hright]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) =
        MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) := by
      rw [Real.volume_Icc]
      norm_num
    rw [hhalf]
    calc
      MeasureTheory.volume (Set.Icc (1 / 2 : ℝ) 1) ≤
          MeasureTheory.volume (⋃ b ∈ v,
            Metric.ball (center b.1) (6 * radius b.1)) := hm
      _ ≤ ∑ b ∈ v, MeasureTheory.volume
          (Metric.ball (center b.1) (6 * radius b.1)) :=
        MeasureTheory.measure_biUnion_finset_le v _
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := by
        simp only [Real.volume_ball]
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [center, radius]
          calc
            ∑ b ∈ v, 2 * (6 * ((b.1.2 - b.1.1) / 2)) =
                ∑ b ∈ v, 6 * (b.1.2 - b.1.1) := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
            _ = 6 * ∑ b ∈ v, (b.1.2 - b.1.1) := by
              rw [Finset.mul_sum]
        · intro b hb
          have := hradius_pos (huBad b.2)
          dsimp [radius] at this
          positivity
      _ = ENNReal.ofReal (6 * ∑ b ∈ v, (b.1.2 - b.1.1)) := rfl
  let e : ↥u ↪ (ℝ × ℝ) := ⟨Subtype.val, Subtype.val_injective⟩
  let F : Finset (ℝ × ℝ) := v.map e
  have hball (p : ℝ × ℝ) :
      Metric.closedBall (center p) (radius p) = Set.Icc p.1 p.2 := by
    rw [Real.closedBall_eq_Icc]
    dsimp [center, radius]
    congr <;> ring
  have hF_bounds : ∀ ⦃z⦄, z ∈ F →
      (1 / 4 : ℝ) ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ 5 / 4 := by
    intro z hz
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hz
    have hbad := huBad b.2
    dsimp [Bad] at hbad
    exact ⟨hbad.1, hbad.2.1.le, hbad.2.2.1⟩
  have hF_disjoint : (SetLike.coe F).PairwiseDisjoint
      (fun z ↦ Set.Icc z.1 z.2) := by
    intro z hz w hw hzw
    obtain ⟨bz, hbz, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨bw, hbw, rfl⟩ := Finset.mem_map.mp hw
    have hne : (bz : ℝ × ℝ) ≠ bw := by
      simpa [e] using hzw
    have hd := huDisjoint bz.2 bw.2 hne
    change Disjoint (Metric.closedBall (center bz) (radius bz))
      (Metric.closedBall (center bw) (radius bw)) at hd
    rw [hball, hball] at hd
    simpa [e] using hd
  have hsum_le : ∑ z ∈ F, (f z.2 - f z.1) ≤ f (5 / 4) - f (1 / 4) := by
    have htel := F.sum_intervalGapsWithin_add_sum_eq_sub rfl
      (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) f
    calc
      ∑ z ∈ F, (f z.2 - f z.1) ≤ _ := by
        rw [le_add_iff_nonneg_left]
        apply Finset.sum_nonneg
        intro i hi
        apply sub_nonneg.mpr
        apply hf
        exact F.intervalGapsWithin_fst_le_snd rfl _ (by norm_num)
          hF_bounds hF_disjoint
      _ = f (5 / 4) - f (1 / 4) := htel
  have hbad_sum : 60 * ∑ b ∈ v, (b.1.2 - b.1.1) <
      ∑ z ∈ F, (f z.2 - f z.1) := by
    rw [Finset.sum_map]
    simp only [e, Function.Embedding.coeFn_mk]
    rw [Finset.mul_sum]
    exact Finset.sum_lt_sum_of_nonempty hv_nonempty
      (fun b hb ↦ (huBad b.2).2.2.2)
  linarith

private theorem log_card_growth_lt_five_mul_rank (B : BohrData G) :
    Real.log ((B.dilate (5 / 4)).carrier.card : ℝ) -
        Real.log ((B.dilate (1 / 4)).carrier.card : ℝ) <
      5 * (max B.rank 1 : ℕ) := by
  let d : ℕ := max B.rank 1
  have hcard : (B.dilate (5 / 4)).carrier.card ≤
      4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card := by
    calc
      (B.dilate (5 / 4)).carrier.card ≤ (B.dilate 2).carrier.card :=
        Finset.card_le_card (carrier_dilate_mono
          (show (5 / 4 : NNReal) ≤ 2 by
            rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
            norm_num))
      _ ≤ 4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card :=
        card_two_le_four_pow_three_rank_mul_card_quarter B
  have hsmall_pos : (0 : ℝ) < (B.dilate (1 / 4)).carrier.card := by
    exact_mod_cast (B.dilate (1 / 4)).carrier_nonempty.card_pos
  have hlarge_pos : (0 : ℝ) < (B.dilate (5 / 4)).carrier.card := by
    exact_mod_cast (B.dilate (5 / 4)).carrier_nonempty.card_pos
  have hlog := Real.log_le_log hlarge_pos (show
      ((B.dilate (5 / 4)).carrier.card : ℝ) ≤
        ((4 ^ (3 * B.rank) * (B.dilate (1 / 4)).carrier.card : ℕ) : ℝ) by
      exact_mod_cast hcard)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (by positivity) hsmall_pos.ne',
    Real.log_pow] at hlog
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by simp [d])
  have hrank_le : (B.rank : ℝ) ≤ d := by
    exact_mod_cast (le_max_left B.rank 1)
  have hlog4 : Real.log (4 : ℝ) < 5 / 3 := by
    rw [Real.log_four_eq]
    linarith [Real.log_two_lt_d9]
  have hmain : (3 * B.rank : ℕ) * Real.log (4 : ℝ) < 5 * d := by
    push_cast
    calc
      3 * (B.rank : ℝ) * Real.log 4 ≤ 3 * d * Real.log 4 := by
        gcongr
      _ < 3 * d * (5 / 3) := by gcongr
      _ = 5 * d := by ring
  dsimp [d] at hmain ⊢
  linarith

/-- The normalized log-cardinality of the real-scale dilates. -/
private noncomputable def normalizedLogCard (B : BohrData G) (s : ℝ) : ℝ :=
  Real.log ((B.dilate s.toNNReal).carrier.card : ℝ) /
    (max B.rank 1 : ℕ)

private theorem normalizedLogCard_monotone (B : BohrData G) :
    Monotone B.normalizedLogCard := by
  intro s t hst
  dsimp [normalizedLogCard]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.log_le_log
  · exact_mod_cast (B.dilate s.toNNReal).carrier_nonempty.card_pos
  · exact_mod_cast Finset.card_le_card
      (carrier_dilate_mono (B := B) (Real.toNNReal_mono hst))

private theorem normalizedLogCard_buffer_growth (B : BohrData G) :
    B.normalizedLogCard (5 / 4) - B.normalizedLogCard (1 / 4) < 5 := by
  have h := log_card_growth_lt_five_mul_rank B
  have hd : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
  have h54 : Real.toNNReal (5 / 4 : ℝ) = (5 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  have h14 : Real.toNNReal (1 / 4 : ℝ) = (1 / 4 : NNReal) := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by norm_num)]
    norm_num
  dsimp [normalizedLogCard]
  rw [h54, h14]
  rw [div_sub_div_same]
  exact (div_lt_iff₀ hd).2 (by simpa [mul_comm] using h)

/-- **Bourgain regular-dilate theorem.** Every finite Bohr datum has a
rank-regular scalar dilate at a scale between `1/2` and `1`. -/
theorem exists_rankRegular_dilate (B : BohrData G) :
    ∃ rho : NNReal, 1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      (B.dilate rho).IsRankRegular := by
  let d : ℕ := max B.rank 1
  obtain ⟨r, hr, hlip⟩ := exists_regular_point_of_monotone
    B.normalizedLogCard (normalizedLogCard_monotone B)
      (normalizedLogCard_buffer_growth B)
  let rho : NNReal := r.toNNReal
  have hrho : (rho : ℝ) = r := Real.coe_toNNReal r (by linarith [hr.1])
  have hrho_half : (1 / 2 : NNReal) ≤ rho := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.1
  have hrho_one : rho ≤ 1 := by
    rw [← NNReal.coe_le_coe, hrho]
    norm_num
    exact hr.2
  refine ⟨rho, hrho_half, hrho_one, ?_⟩
  rw [isRankRegular_dilate_iff]
  dsimp only [rank_dilate]
  intro kappa hkappa
  have hdposN : 0 < d := by simp [d]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  have hkappa_one : kappa ≤ 1 := by
    apply hkappa.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hkappa_real : (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
    exact_mod_cast hkappa
  let sminus : NNReal := (1 - kappa) * rho
  let splus : NNReal := (1 + kappa) * rho
  have hkreal : (kappa : ℝ) ≤ 1 / 100 := by
    calc
      (kappa : ℝ) ≤ 1 / (100 * (d : ℝ)) := hkappa_real
      _ ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        have hd_one : (1 : ℝ) ≤ d := by
          exact_mod_cast (show 1 ≤ d by simp [d])
        nlinarith
  have hrho_real : (1 / 2 : ℝ) ≤ rho ∧ (rho : ℝ) ≤ 1 := by
    exact ⟨by exact_mod_cast hrho_half, by exact_mod_cast hrho_one⟩
  have hsminus_buf : (sminus : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    have hk_lower : (99 / 100 : ℝ) ≤ 1 - (kappa : ℝ) := by
      nlinarith
    constructor
    · calc
        (1 / 4 : ℝ) ≤ (99 / 100) * (1 / 2) := by norm_num
        _ ≤ (1 - (kappa : ℝ)) * (rho : ℝ) := by
          exact mul_le_mul hk_lower hrho_real.1 (by norm_num)
            (sub_nonneg.mpr (by exact_mod_cast hkappa_one))
    · calc
        (1 - (kappa : ℝ)) * (rho : ℝ) ≤ 1 * rho :=
          mul_le_mul_of_nonneg_right (sub_le_self 1 (by positivity)) (by positivity)
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hrho_real.2 (by norm_num)
        _ ≤ 5 / 4 := by norm_num
  have hsplus_buf : (splus : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    dsimp [splus]
    push_cast
    constructor <;> nlinarith
  have hdistminus : |(sminus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [sminus]
    rw [NNReal.coe_sub hkappa_one]
    simp only [NNReal.coe_one]
    change |(1 - (kappa : ℝ)) * (rho : ℝ) - (rho : ℝ)| ≤ (kappa : ℝ)
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 - (kappa : ℝ)) * (rho : ℝ) - rho = -(kappa * rho) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hdistplus : |(splus : ℝ) - r| ≤ (kappa : ℝ) := by
    rw [← hrho]
    dsimp [splus]
    push_cast
    have hrnonneg : (0 : ℝ) ≤ rho := by positivity
    rw [show (1 + (kappa : ℝ)) * (rho : ℝ) - rho = kappa * rho by ring,
      abs_of_nonneg (mul_nonneg (by positivity) hrnonneg)]
    nlinarith [hrho_real.2]
  have hlipminus := hlip (sminus : ℝ) hsminus_buf
  have hlipplus := hlip (splus : ℝ) hsplus_buf
  simp only [normalizedLogCard, Real.toNNReal_coe,
    show r.toNNReal = rho by rfl] at hlipminus hlipplus
  change
    |Real.log ((B.dilate sminus).carrier.card : ℝ) / d -
      Real.log ((B.dilate rho).carrier.card : ℝ) / d| ≤
        60 * |(sminus : ℝ) - r| at hlipminus
  change
    |Real.log ((B.dilate splus).carrier.card : ℝ) / d -
      Real.log ((B.dilate rho).carrier.card : ℝ) / d| ≤
        60 * |(splus : ℝ) - r| at hlipplus
  rw [div_sub_div_same, abs_div, abs_of_pos hdpos] at hlipminus hlipplus
  have hlogminus :
      Real.log ((B.dilate rho).carrier.card : ℝ) -
          Real.log ((B.dilate sminus).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipminus
    calc
      _ ≤ |Real.log ((B.dilate sminus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ)| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      _ ≤ 60 * |(sminus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  have hlogplus :
      Real.log ((B.dilate splus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ) ≤
        60 * d * (kappa : ℝ) := by
    have habs := (div_le_iff₀ hdpos).mp hlipplus
    calc
      _ ≤ |Real.log ((B.dilate splus).carrier.card : ℝ) -
          Real.log ((B.dilate rho).carrier.card : ℝ)| := le_abs_self _
      _ ≤ 60 * |(splus : ℝ) - r| * d := habs
      _ ≤ 60 * (kappa : ℝ) * d := by gcongr
      _ = 60 * d * (kappa : ℝ) := by ring
  let u : ℝ := 100 * d * (kappa : ℝ)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    calc
      100 * (d : ℝ) * (kappa : ℝ) ≤
          100 * d * (1 / (100 * d)) := by gcongr
      _ = 1 := by field_simp
  have hslope : 60 * d * (kappa : ℝ) = (3 / 5 : ℝ) * u := by
    dsimp [u]
    ring
  constructor
  · change (1 - u) * ((B.dilate rho).carrier.card : ℝ) ≤
      ((B.dilate sminus).carrier.card : ℝ)
    by_cases hu : u = 1
    · rw [hu]
      norm_num
    · have hu_lt : u < 1 := lt_of_le_of_ne hu1 hu
      have honeu : 0 < 1 - u := sub_pos.mpr hu_lt
      have hcenter : (0 : ℝ) < (B.dilate rho).carrier.card := by
        exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
      have hinner : (0 : ℝ) < (B.dilate sminus).carrier.card := by
        exact_mod_cast (B.dilate sminus).carrier_nonempty.card_pos
      rw [← Real.log_le_log_iff (mul_pos honeu hcenter) hinner]
      rw [Real.log_mul (sub_ne_zero.mpr (Ne.symm hu)) hcenter.ne']
      have hlogone := Real.log_le_sub_one_of_pos honeu
      rw [hslope] at hlogminus
      nlinarith
  · change ((B.dilate splus).carrier.card : ℝ) ≤
      (1 + u) * ((B.dilate rho).carrier.card : ℝ)
    have hcenter : (0 : ℝ) < (B.dilate rho).carrier.card := by
      exact_mod_cast (B.dilate rho).carrier_nonempty.card_pos
    have houter : (0 : ℝ) < (B.dilate splus).carrier.card := by
      exact_mod_cast (B.dilate splus).carrier_nonempty.card_pos
    rw [← Real.log_le_log_iff houter (mul_pos (by linarith) hcenter)]
    rw [Real.log_mul (by linarith) hcenter.ne']
    have hlogone := Real.le_log_one_add_of_nonneg hu0
    have hfrac : (3 / 5 : ℝ) * u ≤ 2 * u / (u + 2) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    rw [hslope] at hlogplus
    linarith

end BohrData

end

end

/-! ### Upstream module `/tmp/addcombi/AddCombi/Mathlib/Algebra/BigOperators/Ring/Finset.lean` -/

section
open scoped Indicator

section
open _root_.Finset
variable {α R : Type*} [Fintype α] [Semiring R]

@[simp] private lemma _root_.Finset.sum_indicator_one (s : Finset α) : ∑ x, 𝟭_[(s : Set α), R] x = #s := by
  classical simp [Set.indicator_apply]

private lemma _root_.Finset.card_eq_sum_indicator_one (s : Finset α) : #s = ∑ x, 𝟭_[(s : Set α)] x :=
  (sum_indicator_one _).symm

end

end

/-! ### Upstream module `/tmp/addcombi/AddCombi/Mathlib/Algebra/Order/GroupWithZero/Indicator.lean` -/

section
open scoped Indicator

section
open _root_.Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] private lemma _root_.Set.indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  indicator_nonneg (by simp)

@[simp] private lemma _root_.Set.indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[simp]
private lemma _root_.Set.indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/BigOperators/Pi.lean` -/

section
open _root_.Finset _root_.Function
open scoped Indicator

variable {ι α M₀ : Type*}

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] [DecidableEq α]

lemma indicator_one_inf_apply [Fintype α] (s : Finset ι) (t : ι → Finset α) (x : α) :
    𝟭_[↑(s.inf t), M₀] x = ∏ i ∈ s, 𝟭_[t i] x := by simp [Set.indicator_apply, mem_inf, prod_boole]

end CommMonoidWithZero

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Group/Action/Pointwise/Set/Basic.lean` -/

section
open scoped Pointwise Indicator

variable {α G M₀ : Type*}

section OneZero
variable [One M₀] [Zero M₀] [Group G] [MulAction G α]

@[to_additive (dont_translate := M₀) (attr := simp) indicator_one_vadd]
lemma indicator_one_smul (g : G) (s : Set α) (a : α) : 𝟭_[g • s, M₀] a = 𝟭_[s] (g⁻¹ • a) := by
  classical simp [Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem]

end OneZero

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Group/Translate.lean` -/

section
open scoped Pointwise translate Indicator

variable {G M₀ : Type*}

section Semiring
variable [One M₀] [Zero M₀] [AddCommGroup G]

variable (M₀) in
lemma translate_indicator_one (a : G) (s : Set G) : τ a 𝟭_[s, M₀] = 𝟭_[a +ᵥ s] := by
  classical ext; simp [Set.indicator_apply, Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_neg_add]

end Semiring

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Star/Conjneg.lean` -/

section
open scoped ComplexConjugate Indicator

variable {G R : Type*}

section CommSemiring
variable [CommSemiring R] [StarRing R] [AddCommGroup G]

@[simp] lemma conjneg_indicator_one (s : Set G) : conjneg 𝟭_[s, R] = 𝟭_[-s] := by
  classical ext; simp [Set.indicator_apply]

end CommSemiring

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Convolution/Discrete/Basic.lean` -/

section
/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `ddconv`: Discrete convolution of two functions
* `dddconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

## Notation

* `f ∗ᵈ g`: Convolution
* `f ○ᵈ g`: Difference convolution
* `f ∗ᵈ^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

@[expose] public section

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

open _root_.Finset Fintype _root_.Function
open scoped BigOperators ComplexConjugate _root_.NNReal Pointwise translate Indicator

variable {G R γ : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ᵈ g` and difference convolution `f ○ᵈ g` of functions
`f g : G → R`, and show how they interact.
-/

section CommSemiring
variable [CommSemiring R] {f g : G → R}

variable [StarRing R]

lemma indicator_one_dddconv_Set.indicator_apply (s t : Finset G) (a : G) :
    (𝟭_[s, R] ○ᵈ 𝟭_[t]) a = #{x ∈ s ×ˢ t | x.1 - x.2 = a} := by
  simp only [dddconv_apply, Set.indicator_apply, ← ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero, Pi.conj_apply]
  simp_rw [mem_coe, ← mem_product, filter_univ_mem]

end CommSemiring

section Semifield
variable [Semifield R]

@[simp] lemma mu_univ_ddconv_mu_univ : μ_[R] (univ : Finset G) ∗ᵈ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, ddconv_eq_sum_add, card_univ, *]

variable [StarRing R]

@[simp] lemma mu_univ_dddconv_mu_univ : μ_[R] (univ : Finset G) ○ᵈ μ univ = μ univ := by
  ext; cases eq_or_ne (card G : R) 0 <;> simp [mu_apply, dddconv_eq_sum_add, card_univ, *]

end Semifield

section Semifield
variable [Semifield R] [CharZero R]

lemma expect_ddconv (f g : G → R) : 𝔼 a, (f ∗ᵈ g) a = (∑ a, f a) * 𝔼 a, g a := by
  simp_rw [expect, sum_ddconv, mul_smul_comm]

variable [StarRing R]

lemma expect_dddconv (f g : G → R) : 𝔼 a, (f ○ᵈ g) a = (∑ a, f a) * 𝔼 a, conj (g a) := by
  simp_rw [expect, sum_dddconv, mul_smul_comm]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_ddconv (f g : G → R) : balance (f ∗ᵈ g) = balance f ∗ᵈ balance g := by
  simpa [balance, ddconv_sub, sub_ddconv, expect_ddconv]
    using! (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

variable [StarRing R]

@[simp] lemma balance_dddconv (f g : G → R) : balance (f ○ᵈ g) = balance f ○ᵈ balance g := by
  simpa [balance, dddconv_sub, sub_dddconv, expect_dddconv, map_expect]
    using! (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

end Field

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

lemma indicator_one_iterConv_apply (s : Finset G) :
    ∀ (n : ℕ) (a : G), (𝟭_[s, R] ∗ᵈ^ n) a = #{x ∈ s ^^ n | ∑ i, x i = a}
  | 0, a => by simp [apply_ite card, eq_comm]
  | n + 1, a => by
    simp_rw [iterConv_succ', ddconv_eq_sum_sub', indicator_one_iterConv_apply, Set.indicator_apply,
      boole_mul, sum_ite, mem_coe, filter_univ_mem, sum_const_zero, add_zero, ← Nat.cast_sum,
      ← Finset.card_sigma]
    congr 1
    refine card_equiv ((Equiv.sigmaEquivProd ..).trans <| Fin.consEquiv fun _ ↦ G) ?_
    aesop (add simp [Fin.sum_cons, Fin.forall_fin_succ])

lemma indicator_one_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    𝟭_[s] ∗ᵈ^ n ∗ᵈ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [ddconv_eq_sum_sub', indicator_one_iterConv_apply, Finset.sum_apply, translate_apply,
    ← nsmul_eq_mul, ← sum_const, Finset.sum_fiberwise']

variable [StarRing R]

end CommSemiring

section Semifield
variable [Semifield R] [CharZero R]

lemma mu_iterConv_ddconv (s : Finset G) (n : ℕ) (f : G → R) :
    μ s ∗ᵈ^ n ∗ᵈ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  simp only [mu, smul_iterConv, inv_pow, smul_ddconv, indicator_one_iterConv_ddconv, expect,
    card_piFinset_const, Nat.cast_pow]
  rw [← NNRat.cast_smul_eq_nnqsmul R]
  push_cast
  rfl

variable [StarRing R]

end Semifield

section Field
variable [Field R] [CharZero R]

@[simp] lemma balance_iterConv (f : G → R) : ∀ {n}, n ≠ 0 → balance (f ∗ᵈ^ n) = balance f ∗ᵈ^ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterConv_succ _ (n + 1), balance_iterConv _ n.succ_ne_zero]

end Field

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/LpNorm/Compact.lean` -/

section
/-!
# Normalised Lp norms
-/

@[expose] public section

open _root_.Finset hiding card
open _root_.Function _root_.ProbabilityTheory _root_.Real
open Fintype (card)
open scoped BigOperators ComplexConjugate _root_.ENNReal _root_.NNReal Indicator translate

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {α 𝕜 R E : Type*} [MeasurableSpace α]

/-! ### Lp norm -/

section
open _root_.MeasureTheory
section NormedAddCommGroup
variable [NormedAddCommGroup E] {p q : ℝ≥0∞} {f g h : α → E}

/-- The Lp norm of a function with the compact normalisation. -/
private noncomputable def _root_.MeasureTheory.cLpNorm (p : ℝ≥0∞) (f : α → E) : ℝ := lpNorm f p (uniformOn .univ)

scoped notation "‖" f "‖ₙ_[" p "]" => cLpNorm p f

@[simp] private lemma _root_.MeasureTheory.cLpNorm_nonneg : 0 ≤ ‖f‖ₙ_[p] := by simp [cLpNorm]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_exponent_zero (f : α → E) : ‖f‖ₙ_[0] = 0 := by simp [cLpNorm]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_zero (p : ℝ≥0∞) : ‖(0 : α → E)‖ₙ_[p] = 0 := by simp [cLpNorm]
@[simp] private lemma _root_.MeasureTheory.cLpNorm_zero' (p : ℝ≥0∞) : ‖(fun _ ↦ 0 : α → E)‖ₙ_[p] = 0 := by simp [cLpNorm]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : ‖f‖ₙ_[p] = 0 := by
  simp [cLpNorm]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_neg (f : α → E) (p : ℝ≥0∞) : ‖-f‖ₙ_[p] = ‖f‖ₙ_[p] := by simp [cLpNorm]
@[simp] private lemma _root_.MeasureTheory.cLpNorm_neg' (f : α → E) (p : ℝ≥0∞) : ‖fun x ↦ -f x‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp [cLpNorm]

@[simp]
private lemma _root_.MeasureTheory.cLpNorm_norm (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖fun i ↦ ‖f i‖‖ₙ_[p] = ‖f‖ₙ_[p] :=
  lpNorm_norm hf.aestronglyMeasurable _

@[simp]
private lemma _root_.MeasureTheory.cLpNorm_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) : ‖|f|‖ₙ_[p] = ‖f‖ₙ_[p] :=
  lpNorm_abs hf.aestronglyMeasurable _

@[simp]
private lemma _root_.MeasureTheory.cLpNorm_fun_abs {f : α → ℝ} (hf : StronglyMeasurable f) (p : ℝ≥0∞) :
    ‖fun i ↦ |f i|‖ₙ_[p] = ‖f‖ₙ_[p] :=
  lpNorm_fun_abs hf.aestronglyMeasurable _

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

variable [NormedSpace ℝ 𝕜]

end NormedField

section RCLike
variable {p : ℝ≥0∞}

@[simp] private lemma _root_.MeasureTheory.cLpNorm_conj [RCLike R] (f : α → R) : ‖conj f‖ₙ_[p] = ‖f‖ₙ_[p] := lpNorm_conj ..

end RCLike

section DiscreteMeasurableSpace
variable [DiscreteMeasurableSpace α] [Finite α]

end DiscreteMeasurableSpace

variable [Finite α]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_const [Nonempty α] {p : ℝ≥0∞} (hp : p ≠ 0) (a : E) :
    ‖fun _i : α ↦ a‖ₙ_[p] = ‖a‖₊ := by
  cases nonempty_fintype α; simp [cLpNorm, uniformOn, Measure.real, *]

section NormedField
variable [NormedField 𝕜] {p : ℝ≥0∞} {f g : α → 𝕜}

@[simp] private lemma _root_.MeasureTheory.cLpNorm_one [Nonempty α] (hp : p ≠ 0) : ‖(1 : α → 𝕜)‖ₙ_[p] = 1 := by
  cases nonempty_fintype α; simp [cLpNorm, uniformOn, Measure.real, *]

end NormedField

omit [Finite α]
variable [DiscreteMeasurableSpace α] [Fintype α]

private lemma _root_.MeasureTheory.cLpNorm_eq_expect_norm' (hp₀ : p ≠ 0) (hp : p ≠ ∞) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  simp [cLpNorm, uniformOn, lpNorm_eq_integral_norm_rpow_toReal hp₀ hp .of_discrete,
    integral_fintype, cond_apply, expect_eq_sum_div_card, div_eq_inv_mul, ← mul_sum, Measure.real]

private lemma _root_.MeasureTheory.cLpNorm_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] = (𝔼 i, ‖f i‖ ^ (p : ℝ)) ^ (p⁻¹ : ℝ) :=
  cLpNorm_eq_expect_norm' (by simpa using hp) (by simp) _

private lemma _root_.MeasureTheory.cLpNorm_rpow_eq_expect_norm {p : ℝ≥0} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ (p : ℝ) = 𝔼 i, ‖f i‖ ^ (p : ℝ) := by
  rw [cLpNorm_eq_expect_norm hp, Real.rpow_inv_rpow] <;> positivity

private lemma _root_.MeasureTheory.cLpNorm_pow_eq_expect_norm {p : ℕ} (hp : p ≠ 0) (f : α → E) :
    ‖f‖ₙ_[p] ^ p = 𝔼 i, ‖f i‖ ^ p := by
  simpa using cLpNorm_rpow_eq_expect_norm (Nat.cast_ne_zero.2 hp) f

private lemma _root_.MeasureTheory.cL2Norm_sq_eq_expect_norm (f : α → E) : ‖f‖ₙ_[2] ^ 2 = 𝔼 i, ‖f i‖ ^ 2 := by
  simpa using cLpNorm_pow_eq_expect_norm two_ne_zero _

private lemma _root_.MeasureTheory.cL1Norm_eq_expect_norm (f : α → E) : ‖f‖ₙ_[1] = 𝔼 i, ‖f i‖ := by
  simp [cLpNorm_eq_expect_norm']

omit [Fintype α]
variable [Finite α]

private lemma _root_.MeasureTheory.cLpNorm_exponent_top_eq_essSup (f : α → E) : ‖f‖ₙ_[∞] = ⨆ i, ‖f i‖ := by
  cases isEmpty_or_nonempty α <;> simp [cLpNorm, lpNorm_exponent_top_eq_essSup]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_eq_zero (hp : p ≠ 0) : ‖f‖ₙ_[p] = 0 ↔ f = 0 := by
  cases nonempty_fintype α
  simp [cLpNorm, uniformOn, lpNorm_eq_zero .of_discrete hp, ae_eq_top.2, cond_apply]

@[simp] private lemma _root_.MeasureTheory.cLpNorm_pos (hp : p ≠ 0) : 0 < ‖f‖ₙ_[p] ↔ f ≠ 0 :=
  lpNorm_nonneg.lt_iff_ne'.trans (cLpNorm_eq_zero hp).not

@[gcongr] private lemma _root_.MeasureTheory.cLpNorm_mono_right (hpq : p ≤ q) : ‖f‖ₙ_[p] ≤ ‖f‖ₙ_[q] := by
  cases isEmpty_or_nonempty α
  · simp [cLpNorm]
  rw [cLpNorm, cLpNorm, ← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete]
  exact ENNReal.toReal_mono (MemLp.of_discrete (p := q)).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le hpq .of_discrete)

omit [Finite α]

end NormedAddCommGroup
end

section
open Mathlib.Meta.Positivity
open Lean Meta Qq _root_.Function _root_.MeasureTheory

alias ⟨_, cLpNorm_pos_of_ne_zero⟩ := cLpNorm_pos

/-- The `positivity` extension which identifies expressions of the form `‖f‖ₙ_[p]`. -/
@[positivity ‖_‖ₙ_[_]] meta def evalCLpNorm : _root_.Mathlib.Meta.Positivity.PositivityExt where eval {u} R _z _p e :=
  match _p with
  | none => pure .none
  | some _ => do
  match u, R, e with
  | 0, ~q(ℝ), ~q(@cLpNorm $α $E $instαmeas $instEnorm $p $f) =>
    assumeInstancesCommute
    try {
      let some pp := (← core q(inferInstance) (some q(inferInstance)) p).toNonzero | failure
      try
        let _pE ← synthInstanceQ q(PartialOrder $E)
        let _ ← synthInstanceQ q(Finite $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        let some pf := (← core q(inferInstance) (some q(inferInstance)) f).toNonzero | failure
        return .positive q(@cLpNorm_pos_of_ne_zero $α _ _ _ _ _ _ _ $pp $pf)
      catch _ =>
        assumeInstancesCommute
        let some pf ← findLocalDeclWithType? q($f ≠ 0) | failure
        let pf : Q($f ≠ 0) := .fvar pf
        let _ ← synthInstanceQ q(Fintype $α)
        let _ ← synthInstanceQ q(DiscreteMeasurableSpace $α)
        return .positive q(cLpNorm_pos_of_ne_zero $pp $pf)
    } catch _ =>
      return .nonnegative q(cLpNorm_nonneg)
  | _ => throwError "not cLpNorm"

section Examples
section NormedAddCommGroup
variable [Fintype α] [DiscreteMeasurableSpace α] [NormedAddCommGroup E] [PartialOrder E] {f : α → E}

end NormedAddCommGroup

section Complex
variable [Fintype α] [DiscreteMeasurableSpace α] {w : α → ℝ≥0} {f : α → ℂ}

end Complex
end Examples
end

/-! ### Hölder inequality -/

section
open _root_.MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] {p q : ℝ≥0}
  {f g : α → ℝ}

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Finite α] [RCLike 𝕜]
  {p q : ℝ≥0} {f g : α → 𝕜}

end Hoelder

section
variable {α : Type*} {mα : MeasurableSpace α}

@[simp]
private lemma _root_.MeasureTheory.RCLike.cLpNorm_coe_comp [RCLike 𝕜] (p) (f : α → ℝ) : ‖((↑) : ℝ → 𝕜) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  simp only [cLpNorm, lpNorm, comp_def]
  rw! (castMode := .all)
    [RCLike.isUniformEmbedding_ofReal.isEmbedding.aestronglyMeasurable_comp_iff]
  simp [eLpNorm, eLpNorm', eLpNormEssSup]

@[simp] private lemma _root_.MeasureTheory.Complex.cLpNorm_coe_comp (p) (f : α → ℝ) : ‖((↑) : ℝ → ℂ) ∘ f‖ₙ_[p] = ‖f‖ₙ_[p] :=
  RCLike.cLpNorm_coe_comp ..

end
end

section
open _root_.MeasureTheory
variable {ι G 𝕜 E R : Type*} [Fintype ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-! ### Indicator -/

section Indicator
variable [RCLike R] {s : Finset ι} {p : ℝ≥0}

private lemma _root_.MeasureTheory.cLpNorm_rpow_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[(s : Set ι), R]‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simpa [Real.rpow_eq_zero_iff_of_nonneg]
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [cLpNorm_rpow_eq_expect_norm, hp, Set.indicator_apply, apply_ite norm, expect_const,
    nnratCast_dens, hs]

private lemma _root_.MeasureTheory.cLpNorm_pow_indicator_one {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[(s : Set ι), R]‖ₙ_[p] ^ (p : ℝ) = s.dens := by
  simpa using cLpNorm_rpow_indicator_one (Nat.cast_ne_zero.2 hp) s

private lemma _root_.MeasureTheory.cL2Norm_sq_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖ₙ_[2] ^ 2 = s.dens := by
  simpa using cLpNorm_pow_indicator_one two_ne_zero s

@[simp]
private lemma _root_.MeasureTheory.cL2Norm_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖ₙ_[2] = Real.sqrt s.dens := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, cL2Norm_sq_indicator_one] <;> positivity

@[simp] private lemma _root_.MeasureTheory.cL1Norm_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖ₙ_[1] = s.dens := by
  simpa using cLpNorm_pow_indicator_one one_ne_zero s

end Indicator

/-! ### Translation -/

section cLpNorm
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}

@[simp]
private lemma _root_.MeasureTheory.cLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) : ‖τ a f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [cLpNorm_exponent_top_eq_essSup, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_norm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.expect_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] private lemma _root_.MeasureTheory.cLpNorm_conjneg [RCLike E] (f : G → E) : ‖conjneg f‖ₙ_[p] = ‖f‖ₙ_[p] := by
  cases nonempty_fintype G
  simp only [conjneg, cLpNorm_conj]
  obtain p | p := p
  · simp only [cLpNorm_exponent_top_eq_essSup, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [cLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [cLpNorm_eq_expect_norm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.expect_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

end cLpNorm
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/LpNorm/Discrete/Basic.lean` -/

section
/-!
# Lp norms
-/

open _root_.Finset _root_.Function _root_.Real
open scoped BigOperators ComplexConjugate _root_.ENNReal _root_.NNReal Indicator translate

section
open _root_.MeasureTheory
variable {ι G 𝕜 E R : Type*} [Finite ι] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι]

/-! ### Indicator -/

section Indicator
variable [RCLike R] {s : Finset ι} {p : ℝ≥0}

private lemma _root_.MeasureTheory.dLpNorm_rpow_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[(s : Set ι), R]‖_[p] ^ (p : ℝ) = #s := by
  classical
  cases nonempty_fintype ι
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [dLpNorm_rpow_eq_sum_norm, hp, Set.indicator_apply, apply_ite norm, -sum_const,
    card_eq_sum_ones]

private lemma _root_.MeasureTheory.dLpNorm_indicator_one (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[(s : Set ι), R]‖_[p] = #s ^ (p⁻¹ : ℝ) := by
  refine (eq_rpow_inv ?_ ?_ ?_).2 (dLpNorm_rpow_indicator_one ?_ _) <;> positivity

private lemma _root_.MeasureTheory.dLpNorm_pow_indicator_one {p : ℕ} (hp : p ≠ 0) (s : Finset ι) :
    ‖𝟭_[(s : Set ι), R]‖_[p] ^ (p : ℝ) = #s := by
  simpa using dLpNorm_rpow_indicator_one (Nat.cast_ne_zero.2 hp) s

private lemma _root_.MeasureTheory.dL2Norm_sq_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖_[2] ^ 2 = #s := by
  simpa using dLpNorm_pow_indicator_one two_ne_zero s

@[simp] private lemma _root_.MeasureTheory.dL2Norm_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖_[2] = Real.sqrt #s := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, dL2Norm_sq_indicator_one] <;> positivity

@[simp] private lemma _root_.MeasureTheory.dL1Norm_indicator_one (s : Finset ι) : ‖𝟭_[(s : Set ι), R]‖_[1] = #s := by
  simpa using dLpNorm_pow_indicator_one one_ne_zero s

private lemma _root_.MeasureTheory.dLpNorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) : ‖μ_[R] s‖_[p] = #s ^ ((p : ℝ)⁻¹ - 1) := by
  rw [mu, dLpNorm_const_smul ((#s)⁻¹ : R) (𝟭_[(s : Set ι), R]), dLpNorm_indicator_one, norm_inv,
    RCLike.norm_natCast, inv_mul_eq_div, ← Real.rpow_sub_one] <;> positivity

private lemma _root_.MeasureTheory.dLpNorm_mu_le (hp : 1 ≤ p) : ‖μ_[R] s‖_[p] ≤ #s ^ (p⁻¹ - 1 : ℝ) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp only [mu_empty, dLpNorm_zero, card_empty, CharP.cast_eq_zero, NNReal.coe_inv]
    positivity
  · exact (dLpNorm_mu hp hs).le

@[simp] private lemma _root_.MeasureTheory.dL1Norm_mu (hs : s.Nonempty) : ‖μ_[R] s‖_[1] = 1 := by
  simpa using dLpNorm_mu le_rfl hs

private lemma _root_.MeasureTheory.dL1Norm_mu_le_one : ‖μ_[R] s‖_[1] ≤ 1 := by simpa using dLpNorm_mu_le le_rfl

@[simp] private lemma _root_.MeasureTheory.dL2Norm_mu (hs : s.Nonempty) : ‖μ_[R] s‖_[2] = #s ^ (-2⁻¹ : ℝ) := by
  have : (2⁻¹ - 1 : ℝ) = -2⁻¹ := by norm_num
  simpa [sqrt_eq_rpow, this] using dLpNorm_mu one_le_two (R := R) hs

end Indicator

/-! ### Translation -/

section dLpNorm
variable {mG : MeasurableSpace G} [DiscreteMeasurableSpace G] [AddCommGroup G] [Finite G]
  {p : ℝ≥0∞}

@[simp]
private lemma _root_.MeasureTheory.dLpNorm_translate [NormedAddCommGroup E] (a : G) (f : G → E) : ‖τ a f‖_[p] = ‖f‖_[p] := by
  cases nonempty_fintype G
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_norm, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_norm hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] private lemma _root_.MeasureTheory.dLpNorm_conjneg [RCLike E] (f : G → E) : ‖conjneg f‖_[p] = ‖f‖_[p] := by
  cases nonempty_fintype G
  simp only [conjneg, dLpNorm_conj]
  obtain p | p := p
  · simp only [dLinftyNorm_eq_iSup_norm, ENNReal.none_eq_top]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [dLpNorm_exponent_zero, ENNReal.some_eq_coe, ENNReal.coe_zero]
  · simp only [dLpNorm_eq_sum_norm hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

private lemma _root_.MeasureTheory.dLpNorm_translate_sum_sub_le [NormedAddCommGroup E] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → G) (f : G → E) : ‖τ (∑ i ∈ s, a i) f - f‖_[p] ≤ ∑ i ∈ s, ‖τ (a i) f - f‖_[p] := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s ih hs =>
  calc
    _ = ‖τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)‖_[p] := by
      rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ∑ j ∈ s, ‖(τ (a j) f - f)‖_[p] := by
      grw [dLpNorm_add_le hp, hs]
    _ = _ := by rw [dLpNorm_translate, sum_cons]

end dLpNorm
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Convolution/Norm.lean` -/

section
/-!
# Norm of a convolution

This file characterises the L1-norm of the convolution of two functions and proves the Young
convolution inequality.
-/

@[expose] public section

open _root_.Finset _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped ComplexConjugate _root_.ENNReal _root_.NNReal Pointwise translate

variable {G 𝕜 : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section RCLike
variable [RCLike 𝕜] {p : ℝ≥0∞}

lemma dddconv_eq_wInner_one (f g : G → 𝕜) (a : G) : (f ○ᵈ g) a = conj ⟪f, τ a g⟫_[𝕜] := by
  simp [wInner_one_eq_sum, dddconv_eq_sum_sub', map_sum, mul_comm]

lemma wInner_one_dddconv (f g h : G → 𝕜) : ⟪f, g ○ᵈ h⟫_[𝕜] = ⟪conj g, conj f ∗ᵈ conj h⟫_[𝕜] := by
  calc
    _ = ∑ b, ∑ a, g a * conj (h b) * conj (f (a - b)) := by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_dddconv_mul]
      exact sum_comm
    _ = ∑ b, ∑ a, conj (f a) * conj (h b) * g (a + b) := by
      simp_rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv ((Equiv.refl _).prodShear Equiv.subRight) _ _
        (by simp [mul_rotate, mul_right_comm])
    _ = _ := by
      simp_rw [wInner_one_eq_sum, RCLike.inner_apply, sum_ddconv_mul, Pi.conj_apply,
        RCLike.conj_conj]
      exact sum_comm

lemma wInner_one_ddconv (f g h : G → 𝕜) : ⟪f, g ∗ᵈ h⟫_[𝕜] = ⟪conj g, conj f ○ᵈ conj h⟫_[𝕜] := by
  simp_rw [wInner_one_dddconv, RCLike.conj_conj]

lemma dddconv_wInner_one (f g h : G → 𝕜) : ⟪f ○ᵈ g, h⟫_[𝕜] = ⟪conj h ∗ᵈ conj g, conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_dddconv, conj_wInner_symm]

lemma ddconv_wInner_one (f g h : G → 𝕜) : ⟪f ∗ᵈ g, h⟫_[𝕜] = ⟪conj h ○ᵈ conj g, conj f⟫_[𝕜] := by
  rw [← conj_wInner_symm, wInner_one_ddconv, conj_wInner_symm]

lemma dddconv_wInner_one_eq_wInner_one_ddconv (f g h : G → 𝕜) :
    ⟪f ○ᵈ g, h⟫_[𝕜] = ⟪f, h ∗ᵈ g⟫_[𝕜] := by
  rw [dddconv_wInner_one]; simp [wInner_one_eq_sum, mul_comm]

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

omit [Fintype G] in
@[simp] lemma dLpNorm_trivChar [Finite G] (hp : p ≠ 0) : ‖(trivChar : G → 𝕜)‖_[p] = 1 := by
  cases nonempty_fintype G
  obtain _ | p := p
  · simp only [ENNReal.none_eq_top, dLinftyNorm_eq_iSup_norm, trivChar_apply, apply_ite,
      norm_one, norm_zero]
    exact IsLUB.ciSup_eq ⟨by aesop (add simp mem_upperBounds), fun x hx ↦ hx ⟨0, if_pos rfl⟩⟩
  · simp at hp
    simp [dLpNorm_eq_sum_norm hp, apply_ite, hp]

/-- A special case of **Young's convolution inequality**. -/
lemma dLpNorm_ddconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : G → 𝕜) :
    ‖f ∗ᵈ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] := by
  obtain rfl | hp := hp.eq_or_lt
  · simp_rw [ENNReal.coe_one, dL1Norm_eq_sum_norm, sum_mul_sum, ddconv_eq_sum_sub']
    calc
      ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x, ∑ y, ‖f y * g (x - y)‖ :=
        sum_le_sum fun x _ ↦ norm_sum_le _ _
      _ = _ := ?_
    rw [sum_comm]
    simp_rw [norm_mul]
    exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun _ ↦ rfl
  have hp₀ := zero_lt_one.trans hp
  rw [← rpow_le_rpow_iff _ _ hp₀, mul_rpow]
  any_goals positivity
  dsimp
  simp_rw [dLpNorm_rpow_eq_sum_norm hp₀.ne', ddconv_eq_sum_sub']
  have hpconj : (p : ℝ).HolderConjugate (1 - (p : ℝ)⁻¹)⁻¹ :=
    ⟨by simp, mod_cast hp₀, by bound⟩
  have (x : G) : ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
      (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) := by
    rw [← le_rpow_inv_iff_of_pos, mul_rpow, ← rpow_mul, sub_one_mul, mul_inv_cancel₀]
    any_goals positivity
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ := norm_sum_le _ _
      _ = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p : ℝ)⁻¹ * ‖g (x - y)‖ ^ (1 - (p : ℝ)⁻¹) := ?_
      _ ≤ _ := inner_le_Lp_mul_Lq _ _ _ hpconj
      _ = _ := ?_
    · congr with t
      rw [norm_mul, mul_assoc, ← rpow_add' (by positivity), add_sub_cancel, rpow_one]
      simp
    · have : 1 - (p : ℝ)⁻¹ ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 <| NNReal.coe_ne_one.2 hp.ne').symm
      simp [mul_rpow, rpow_nonneg, hp₀.ne', this, abs_rpow_of_nonneg]
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
        ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ) :=
      sum_le_sum fun i _ ↦ this _
    _ = _ := ?_
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subLeft _) _ _ fun _ ↦ rfl
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = ‖g‖_[1] := by
    simp_rw [dL1Norm_eq_sum_norm]
    exact fun x ↦ Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl
  simp_rw [hg]
  rw [← sum_mul, sum_comm]
  simp_rw [← mul_sum, hg']
  rw [← sum_mul, mul_assoc, ← rpow_one_add' (by positivity), add_sub_cancel]
  rw [add_sub_cancel]
  positivity

end RCLike

section Real
variable [MeasurableSpace G] [DiscreteMeasurableSpace G] {f g : G → ℝ} {n : ℕ}

--TODO: Include `f : G → ℂ`
lemma dL1Norm_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ∗ᵈ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := fun x ↦ sum_nonneg fun y _ ↦ mul_nonneg (hf _) (hg _)
  simp [dL1Norm_eq_sum_norm, ← sum_ddconv, ddconv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)]

lemma dL1Norm_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ○ᵈ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] := by
  simpa using dL1Norm_ddconv hf (conjneg_nonneg.2 hg)

end Real

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Convolution/Order.lean` -/

section
@[expose] public section

open _root_.Finset _root_.Function _root_.Real
open scoped ComplexConjugate _root_.NNReal Pointwise

variable {G R : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

lemma ddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ᵈ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

lemma ddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ∗ᵈ g) a :=
  ddconv_nonneg hf hg _

variable [StarRing R] [StarOrderedRing R]

lemma dddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ᵈ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _

lemma dddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (f ○ᵈ g) a :=
  dddconv_nonneg hf hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g : G → R}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care
@[simp] lemma support_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) :
    support (f ∗ᵈ g) = support f + support g := by
  refine (support_ddconv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, ddconv_apply_add]
  exact ne_of_gt <| sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩

lemma ddconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ᵈ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨ddconv_nonneg hf hg, a + b, ?_⟩
  rw [ddconv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

variable [StarRing R] [StarOrderedRing R]

@[simp]
lemma support_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ᵈ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_ddconv hf (conjneg_nonneg.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗ᵈ^ n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => ddconv_nonneg (iterConv_nonneg hf) hf

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R} {n : ℕ}

@[simp] lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗ᵈ^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => ddconv_pos (iterConv_pos hf) hf

end StrictOrderedCommSemiring

section
open Mathlib.Meta.Positivity
open Lean Meta Qq _root_.Function

section
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}

variable [StarRing R] [StarOrderedRing R]

end
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R}

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Physics/DRC.lean` -/

section
/-!
# Dependent Random Choice
-/

open _root_.Finset Fintype _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped _root_.ENNReal _root_.NNReal Indicator Pointwise

variable {G : Type*} [DecidableEq G] [Fintype G] [AddCommGroup G] {p : ℕ} {B₁ B₂ A : Finset G}
  {ε δ : ℝ}

/-- Auxiliary definition for the Dependent Random Choice step. We intersect `B₁` and `B₂` with
`c p A s` for some `s`. -/
private def c (p : ℕ) (A : Finset G) (s : Fin p → G) : Finset G := univ.inf fun i ↦ s i +ᵥ A

set_option backward.isDefEq.respectTransparency false in
private lemma lemma_0 (p : ℕ) (B₁ B₂ A : Finset G) (f : G → ℝ) :
    ∑ s, ⟪𝟭_[↑(B₁ ∩ c p A s), ℝ] ○ᵈ 𝟭_[↑(B₂ ∩ c p A s)], f⟫_[ℝ] =
      (#B₁ * #B₂) • ∑ x, (μ_[ℝ] B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * f x := by
  simp_rw [mul_assoc]
  simp only [wInner_one_eq_sum, inner_apply', RCLike.conj_to_real, mul_sum, sum_mul, smul_sum,
    @sum_comm _ _ (Fin p → G), sum_dddconv_mul, dddconv_apply_sub, Fintype.sum_pow,
    Set.map_indicator_one]
  congr with b₁
  congr with b₂
  refine Fintype.sum_equiv (Equiv.neg _) _ _ fun s ↦ ?_
  rw [← smul_mul_assoc, mul_smul_mul_comm, card_smul_mu_apply, card_smul_mu_apply,
    coe_inter, coe_inter, Set.indicator_one_inter_apply, Set.indicator_one_inter_apply,
    mul_mul_mul_comm, prod_mul_distrib]
  simp [c, indicator_one_inf_apply, sub_eq_add_neg, mul_assoc, add_comm]

private lemma sum_c (p : ℕ) (B A : Finset G) : ∑ s, #(B ∩ c p A s) = #A ^ p * #B := by
  simp only [card_eq_sum_indicator_one, Set.indicator_one_inter_apply, c, indicator_one_inf_apply,
    mul_sum, sum_mul, coe_inter, coe_vadd_finset, sum_pow', @sum_comm G, Fintype.piFinset_univ,
    ← translate_indicator_one, translate_apply]
  congr with x
  exact Fintype.sum_equiv (Equiv.subLeft fun _ ↦ x) _ _ fun s ↦ mul_comm _ _

private lemma sum_cast_c (p : ℕ) (B A : Finset G) :
    ∑ s, (#(B ∩ c p A s) : ℝ) = #A ^ p * #B := by
  rw [← Nat.cast_sum, sum_c]; norm_cast

variable [MeasurableSpace G]

noncomputable def s (p : ℝ≥0) (ε : ℝ) (B₁ B₂ A : Finset G) : Finset G :=
  {x | (1 - ε) * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] < (𝟭_[A] ○ᵈ 𝟭_[A]) x}

@[simp]
lemma mem_s {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : Finset G} {x : G} :
    x ∈ s p ε B₁ B₂ A ↔
      (1 - ε) * ‖𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] < (𝟭_[A] ○ᵈ 𝟭_[A]) x := by simp [s]

lemma mem_s' {p : ℝ≥0} {ε : ℝ} {B₁ B₂ A : Finset G} {x : G} :
    x ∈ s p ε B₁ B₂ A ↔ (1 - ε) * ‖μ_[ℝ] A ○ᵈ μ A‖_[p, μ B₁ ○ᵈ μ B₂] < (μ A ○ᵈ μ A) x := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · simp
  · simp [← card_smul_mu, -nsmul_eq_mul, smul_dddconv, dddconv_smul, wLpNorm_nsmul, hA.card_pos]

variable [DiscreteMeasurableSpace G]

set_option backward.isDefEq.respectTransparency false in
/-- If `A` is nonempty, and `B₁` and `B₂` intersect, then the `μ B₁ ○ᵈ μ B₂`-weighted Lp norm of
`𝟭_[A] ○ᵈ 𝟭_[A]` is positive. -/
private lemma dLpNorm_ddconv_pos (hp : p ≠ 0) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    (0 : ℝ) < ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
  rw [wLpNorm_pow_eq_sum_norm (by positivity)]
  refine sum_pos' (fun x _ ↦ by positivity) ⟨0, mem_univ _, smul_pos ?_ <| pow_pos ?_ _⟩
  · rwa [pos_iff_ne_zero, ← Function.mem_support, support_dddconv, support_mu, support_mu,
      ← coe_sub, mem_coe, zero_mem_sub_iff, not_disjoint_iff_nonempty_inter] <;> exact mu_nonneg
  · rw [norm_pos_iff, ← Function.mem_support, support_dddconv, Set.support_indicator_one]
    any_goals exact Set.indicator_one_nonneg -- positivity
    exact hA.to_set.zero_mem_sub

set_option backward.isDefEq.respectTransparency false in
lemma drc (hp₂ : 2 ≤ p) (f : G → ℝ≥0) (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∈ f.support)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      ⟪μ_[ℝ] A₁ ○ᵈ μ A₂, (↑) ∘ f⟫_[ℝ] * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p
        ≤ 2 * ∑ x, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A, ℝ] ○ᵈ 𝟭_[A]) x ^ p * f x ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
        ≤ #A₁ / #B₁ ∧
      (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
        ≤ #A₂ / #B₂ := by
  have := hB.mono inter_subset_left
  have := hB.mono inter_subset_right
  have hp₀ : p ≠ 0 := by positivity
  have := dLpNorm_ddconv_pos hp₀ hB hA
  set M : ℝ :=
    2 ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p * (Real.sqrt #B₁ * Real.sqrt #B₂) / #A ^ p
      with hM_def
  have hM : 0 < M := by rw [hM_def]; positivity
  replace hf : 0 < ∑ x, (μ_[ℝ] B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p * f x := by
    have : 0 ≤ μ_[ℝ] B₁ ○ᵈ μ B₂ * (𝟭_[A] ○ᵈ 𝟭_[A]) ^ p * (↑) ∘ f := -- positivity
      mul_nonneg (mul_nonneg (dddconv_nonneg mu_nonneg mu_nonneg) <| pow_nonneg
        (dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg) _) fun _ ↦ by simp
    refine Fintype.sum_pos <| this.lt_iff_ne'.2 <| support_nonempty_iff.1 ?_
    simp only [support_comp_eq, Set.Nonempty, and_assoc, support_mul', support_dddconv,
      Set.indicator_one_nonneg, mu_nonneg, Set.support_indicator_one, support_mu,
      NNReal.coe_eq_zero,iff_self, forall_const, Set.mem_inter_iff, ← coe_sub, mem_coe,
      support_pow' _ hp₀, hf]
  set A₁ := fun s ↦ B₁ ∩ c p A s
  set A₂ := fun s ↦ B₂ ∩ c p A s
  set g : (Fin p → G) → ℝ := fun s ↦ #(A₁ s) * #(A₂ s) with hg_def
  have hg : ∀ s, 0 ≤ g s := fun s ↦ by rw [hg_def]; dsimp; positivity
  have hgB : ∑ s, g s = #B₁ * #B₂ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
    have hAdddconv : 0 ≤ 𝟭_[(A : Set G), ℝ] ○ᵈ 𝟭_[A] :=
      dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg
    simpa only [wLpNorm_pow_eq_sum_norm hp₀, norm_of_nonneg (hAdddconv _), NNReal.smul_def,
      NNReal.coe_dddconv, NNReal.coe_comp_mu, wInner_one_eq_sum, Pi.one_apply, inner_apply',
      ← coe_inter, conj_to_real, mul_one, sum_dddconv, sum_indicator_one, nsmul_eq_mul,
      Nat.cast_mul, g, A₁, A₂] using! lemma_0 p B₁ B₂ A 1
  suffices ∑ s, ⟪𝟭_[A₁ s, ℝ] ○ᵈ 𝟭_[A₂ s], (↑) ∘ f⟫_[ℝ] * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p
    < ∑ s, 𝟭_[({s | M ^ 2 ≤ g s} : Finset _)] s * g s *
        (2 * ∑ x, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A, ℝ] ○ᵈ 𝟭_[A]) x ^ p * f x) by
    obtain ⟨s, -, hs⟩ := exists_lt_of_sum_lt this
    refine ⟨_, inter_subset_left (s₂ := c p A s), _, inter_subset_left (s₂ := c p A s), ?_⟩
    simp only [Set.indicator_apply, boole_mul] at hs
    split_ifs at hs with h; swap
    · simp only [zero_mul, wInner_one_eq_sum, Function.comp_apply, RCLike.inner_apply',
        RCLike.conj_to_real] at hs
      have : 0 ≤ 𝟭_[(A₁ s : Set G), ℝ] ○ᵈ 𝟭_[A₂ s] :=
        dddconv_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg
      -- positivity
      cases hs.not_ge <|
        mul_nonneg (sum_nonneg fun x _ ↦ mul_nonneg (this _) <| by positivity) <| by positivity
    have : (4 : ℝ) ⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p)
      ≤ #(A₁ s) / #B₁ * (#(A₂ s) / #B₂) := by
      rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
      simpa [hg_def, hM_def, mul_pow, div_pow, pow_mul', show (2 : ℝ) ^ 2 = 4 by norm_num,
        mul_div_right_comm] using h
    refine ⟨(lt_of_mul_lt_mul_left (hs.trans_eq' ?_) <| hg s).le, this.trans <|
      mul_le_of_le_one_right ?_ <| div_le_one_of_le₀ ?_ ?_, this.trans <|
      mul_le_of_le_one_left ?_ <| div_le_one_of_le₀ ?_ ?_⟩
    · simp_rw [A₁, A₂, g, ← card_smul_mu, smul_dddconv, dddconv_smul, ← Nat.cast_smul_eq_nsmul ℝ,
        wInner_smul_left, smul_eq_mul, star_trivial, mul_assoc, A₁, A₂]
    any_goals positivity
    all_goals exact Nat.cast_le.2 <| card_mono inter_subset_left
  rw [← sum_mul, lemma_0, nsmul_eq_mul, Nat.cast_mul, ← sum_mul, mul_right_comm, ← hgB,
    mul_left_comm, ← mul_assoc]
  simp only [Set.indicator_apply, boole_mul, mem_coe, mem_filter, mem_univ, true_and, ← sum_filter,
    mul_lt_mul_iff_left₀ hf, Function.comp_apply]
  by_cases h : ∀ s, g s ≠ 0 → M ^ 2 ≤ g s
  · rw [← sum_filter_ne_zero (s := filter _ _), Finset.filter_comm,
      filter_true_of_mem fun s hs ↦ h s (mem_filter.1 hs).2, ← sum_filter_ne_zero]
    refine lt_mul_of_one_lt_left (sum_pos (fun s hs ↦ (h _ (mem_filter.1 hs).2).trans_lt' <|
      by positivity) ?_) one_lt_two
    rw [← sum_filter_ne_zero] at hgB
    exact nonempty_of_sum_ne_zero <| hgB.trans_ne <| by positivity
  push Not at h
  obtain ⟨s, hs⟩ := h
  suffices h : (2 : ℝ) * ∑ s with g s < M ^ 2, g s < ∑ s, g s by
    refine (le_or_lt_of_add_le_add ?_).resolve_left h.not_ge
    simp_rw [← not_le, ← compl_filter, ← two_mul, ← mul_add, sum_compl_add_sum]
    rfl
  rw [← lt_div_iff₀' (zero_lt_two' ℝ), div_eq_inv_mul]
  calc
    ∑ s with g s < M ^ 2, g s = ∑ s with g s < M ^ 2 ∧ g s ≠ 0, Real.sqrt (g s) * Real.sqrt (g s)
          := by simp_rw [mul_self_sqrt (hg _), ← filter_filter, sum_filter_ne_zero]
    _ < ∑ s with g s < M ^ 2 ∧ g s ≠ 0, M * Real.sqrt (g s)
        := sum_lt_sum_of_nonempty ⟨s, mem_filter.2 ⟨mem_univ _, hs.symm⟩⟩ ?_
    _ ≤ ∑ s, M * Real.sqrt (g s) := sum_le_univ_sum_of_nonneg fun s ↦ by positivity
    _ = M * (∑ s, Real.sqrt #(A₁ s) * Real.sqrt #(A₂ s))
        := by simp_rw [mul_sum, g, sqrt_mul <| Nat.cast_nonneg _]
    _ ≤ M * (Real.sqrt (∑ s, #(A₁ s)) * Real.sqrt (∑ s, #(A₂ s))) := by
      gcongr; exact sum_sqrt_mul_sqrt_le _ fun i ↦ by positivity fun i ↦ by positivity
    _ = _ := ?_
  · simp only [mem_filter, mem_univ, true_and, and_imp]
    exact fun s hsM hs ↦ mul_lt_mul_of_pos_right ((sqrt_lt' hM).2 hsM) <|
      sqrt_pos.2 <| (hg _).lt_of_ne' hs
  rw [sum_cast_c, sum_cast_c, sqrt_mul', sqrt_mul', mul_mul_mul_comm (Real.sqrt _), mul_self_sqrt,
    ← mul_assoc, hM_def, div_mul_cancel₀, ← sqrt_mul, mul_assoc, mul_self_sqrt, hgB, mul_right_comm,
    mul_assoc]
  all_goals positivity

set_option backward.isDefEq.respectTransparency false in
--TODO: When `1 < ε`, the result is trivial since `S = univ`.
lemma sifting (B₁ B₂ : Finset G) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ) (hp : Even p)
    (hp₂ : 2 ≤ p) (hpε : ε⁻¹ * log (2 / δ) ≤ p) (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∉ s p ε B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧ 1 - δ ≤ ∑ x ∈ s p ε B₁ B₂ A, (μ A₁ ○ᵈ μ A₂) x ∧
        (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
            #A₁ / #B₁ ∧
          (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
            #A₂ / #B₂ := by
  obtain ⟨A₁, hAB₁, A₂, hAB₂, h, hcard₁, hcard₂⟩ :=
    drc hp₂ 𝟭_[(s p ε B₁ B₂ A)ᶜ]
      (by simpa only [Set.support_indicator_one, coe_compl, Set.mem_compl_iff, mem_coe]) hB hA
  refine ⟨A₁, hAB₁, A₂, hAB₂, ?_, hcard₁, hcard₂⟩
  have hp₀ : 0 < p := by positivity
  have aux (c : Finset G) (r)
    (h : (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤ #c / r) :
    c.Nonempty := by
    simp_rw [nonempty_iff_ne_empty]
    rintro rfl
    simp [pow_mul', inv_mul_le_iff₀ (zero_lt_four' ℝ), div_nonpos_iff,
      (pow_pos (dLpNorm_ddconv_pos hp₀.ne' hB hA) 2).not_ge, hp₀.ne', hA.ne_empty] at h
  have hA₁ : A₁.Nonempty := aux _ _ hcard₁
  have hA₂ : A₂.Nonempty := aux _ _ hcard₂
  clear hcard₁ hcard₂ aux
  rw [sub_le_comm]
  calc
    _ = ∑ x ∈ (s p ε B₁ B₂ A)ᶜ, (μ A₁ ○ᵈ μ A₂) x := ?_
    _ = ⟪μ_[ℝ] A₁ ○ᵈ μ A₂, (↑) ∘ 𝟭_[(s (↑p) ε B₁ B₂ A)ᶜ, ℝ≥0]⟫_[ℝ] := by
      simp [wInner_one_eq_sum, -mem_compl, -mem_s, Set.indicator_apply]
      simp only [← ite_not (_ ∈ s p ε B₁ B₂ A), ← mem_compl, apply_ite]
      simp [-mem_compl]
    _ ≤ _ := (le_div_iff₀ <| dLpNorm_ddconv_pos hp₀.ne' hB hA).2 h
    _ ≤ _ := ?_
  · simp_rw [sub_eq_iff_eq_add', sum_add_sum_compl, sum_dddconv, map_mu]
    rw [sum_mu _ hA₁, sum_mu _ hA₂, one_mul]
  rw [div_le_iff₀ (dLpNorm_ddconv_pos hp₀.ne' hB hA), ← le_div_iff₀' (zero_lt_two' ℝ)]
  simp only [apply_ite NNReal.toReal, Set.indicator_apply, NNReal.coe_one, NNReal.coe_zero,
    mul_boole, Fintype.sum_ite_mem, mul_div_right_comm, ← coe_compl, mem_coe]
  calc
    ∑ x ∈ (s p ε B₁ B₂ A)ᶜ, (μ B₁ ○ᵈ μ B₂) x * (𝟭_[A] ○ᵈ 𝟭_[A]) x ^ p ≤
        ∑ x ∈ (s p ε B₁ B₂ A)ᶜ,
          (μ B₁ ○ᵈ μ B₂) x * ((1 - ε) * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]) ^ p := by
      gcongr with x hx
      · exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
      · exact dddconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg _
      · simpa using hx
    _ ≤ ∑ x, (μ B₁ ○ᵈ μ B₂) x * ((1 - ε) * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]) ^ p := by
      gcongr
      · intros
        exact mul_nonneg (dddconv_apply_nonneg mu_nonneg mu_nonneg _) <| hp.pow_nonneg _
      · exact subset_univ _
    _ = ‖μ_[ℝ] B₁‖_[1] * ‖μ_[ℝ] B₂‖_[1] * ((1 - ε) ^ p * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p)
        := ?_
    _ ≤ _ :=
      mul_le_of_le_one_left (mul_nonneg (hp.pow_nonneg _) <| hp.pow_nonneg _) <|
        mul_le_one₀ dL1Norm_mu_le_one (by positivity) dL1Norm_mu_le_one
    _ ≤ _ := mul_le_mul_of_nonneg_right ?_ <| hp.pow_nonneg _
  · have : 0 ≤ μ_[ℝ] B₁ ○ᵈ μ B₂ := dddconv_nonneg mu_nonneg mu_nonneg
    simp_rw [← dL1Norm_dddconv mu_nonneg mu_nonneg, dL1Norm_eq_sum_norm,
      norm_of_nonneg (this _), sum_mul, mul_pow]
  calc
    (1 - ε) ^ p ≤ exp (-ε) ^ p := by gcongr; exact one_sub_le_exp_neg _
    _ = exp (-(ε * p)) := by rw [← neg_mul, exp_mul, rpow_natCast]
    _ ≤ exp (-log (2 / δ)) :=
      (exp_monotone <| neg_le_neg <| (inv_mul_le_iff₀ <| by positivity).1 hpε)
    _ = δ / 2 := by rw [exp_neg, exp_log, inv_div]; positivity

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Sifting.lean` -/

section
/-!
# Dependent random choice / sifting for Erdős Problem 140

This file proves the finite averaging argument used in the Kelley--Meka
sifting step.  All averages are written with their denominators visible.  In
particular, `rawPairAverage` divides by `|G|^2`, while
`pairProbability` divides by `|A₁||A₂|`.  The exact identity below therefore
contains the normalization factor `|G|^2 / (|B₁||B₂|)`.
-/

open scoped BigOperators
open _root_.Finset

namespace Sifting

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

noncomputable section

/-- The elements of `B` lying in every translate `A + sᵢ`. -/
def siftedSet (A B : Finset G) {p : ℕ} (s : Fin p → G) : Finset G :=
  B.filter fun b ↦ ∀ i, b - s i ∈ A

theorem siftedSet_subset (A B : Finset G) {p : ℕ} (s : Fin p → G) :
    siftedSet A B s ⊆ B := by
  intro b hb
  exact (mem_filter.mp hb).1

@[simp] theorem mem_siftedSet {A B : Finset G} {p : ℕ} {s : Fin p → G} {b : G} :
    b ∈ siftedSet A B s ↔ b ∈ B ∧ ∀ i, b - s i ∈ A := by
  simp [siftedSet]

/-- The unnormalised weighted count of ordered differences from two sets. -/
def pairSum (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  ∑ a₁ ∈ A₁, ∑ a₂ ∈ A₂, F (a₁ - a₂)

/-- The pair count divided by `|G|^2`.  This is
`⟨¹_A₁ ∘ ¹_A₂, F⟩` with normalized ambient averages. -/
def rawPairAverage (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  pairSum A₁ A₂ F / (Fintype.card G : ℝ) ^ 2

/-- The uniform probability average over ordered pairs from two nonempty sets.
It is defined as zero when a denominator vanishes. -/
def pairProbability (A₁ A₂ : Finset G) (F : G → ℝ) : ℝ :=
  pairSum A₁ A₂ F / ((A₁.card : ℝ) * A₂.card)

/-- The set of differences which can occur between `A₁` and `A₂`. -/
def differenceSet (A₁ A₂ : Finset G) : Finset G :=
  A₁.biUnion fun a₁ ↦ A₂.image fun a₂ ↦ a₁ - a₂

@[simp] theorem mem_differenceSet {A₁ A₂ : Finset G} {x : G} :
    x ∈ differenceSet A₁ A₂ ↔ ∃ a₁ ∈ A₁, ∃ a₂ ∈ A₂, a₁ - a₂ = x := by
  simp [differenceSet]

/-- The number of shifts putting both endpoints of a difference in `A`. -/
def commonShiftCount (A : Finset G) (x : G) : ℕ :=
  #(Finset.univ.filter fun t : G ↦ x - t ∈ A ∧ -t ∈ A)

private theorem sum_pair_shift_indicator (A : Finset G) (b₁ b₂ : G) :
    (∑ s : G, if b₁ - s ∈ A ∧ b₂ - s ∈ A then (1 : ℝ) else 0) =
      commonShiftCount A (b₁ - b₂) := by
  rw [commonShiftCount]
  let e : G ≃ G := Equiv.subRight b₂
  rw [show ((#(Finset.univ.filter fun t : G ↦ b₁ - b₂ - t ∈ A ∧ -t ∈ A) : ℕ) : ℝ) =
      ∑ t : G, if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0 by
    simpa using (Finset.sum_boole
      (fun t : G ↦ b₁ - b₂ - t ∈ A ∧ -t ∈ A) (Finset.univ : Finset G) :
        (∑ t ∈ (Finset.univ : Finset G),
          if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0) = _)]
  refine Fintype.sum_equiv e
    (fun s : G ↦ if b₁ - s ∈ A ∧ b₂ - s ∈ A then (1 : ℝ) else 0)
    (fun t : G ↦ if b₁ - b₂ - t ∈ A ∧ -t ∈ A then (1 : ℝ) else 0)
    (fun t ↦ ?_)
  change (if b₁ - t ∈ A ∧ b₂ - t ∈ A then (1 : ℝ) else 0) =
    if b₁ - b₂ - (t - b₂) ∈ A ∧ -(t - b₂) ∈ A then 1 else 0
  have h₁ : b₁ - b₂ - (t - b₂) = b₁ - t := by abel
  have h₂ : -(t - b₂) = b₂ - t := by abel
  rw [h₁, h₂]

private theorem sum_all_coordinate_indicators (A : Finset G) (b₁ b₂ : G) (p : ℕ) :
    (∑ s : Fin p → G,
        if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) =
      (commonShiftCount A (b₁ - b₂) : ℝ) ^ p := by
  let D : Finset G := Finset.univ.filter fun t : G ↦ b₁ - t ∈ A ∧ b₂ - t ∈ A
  have hsets :
      Finset.univ.filter
          (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A) =
        Fintype.piFinset (fun _ : Fin p ↦ D) := by
    ext s
    simp [D, Fintype.mem_piFinset]
  calc
    (∑ s : Fin p → G,
        if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) =
        ((Finset.univ.filter
          (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A)).card : ℝ) := by
      simpa using (Finset.sum_boole
        (fun s : Fin p → G ↦ ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A)
        (Finset.univ : Finset (Fin p → G)) :
          (∑ s ∈ (Finset.univ : Finset (Fin p → G)),
            if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0) = _)
    _ = ((Fintype.piFinset fun _ : Fin p ↦ D).card : ℝ) := by rw [hsets]
    _ = (D.card : ℝ) ^ p := by simp [Fintype.card_piFinset]
    _ = (commonShiftCount A (b₁ - b₂) : ℝ) ^ p := by
      congr 1
      have hsum := sum_pair_shift_indicator A b₁ b₂
      simpa [D] using hsum

/-- The raw dependent-random-choice expansion before dividing by any
probability normalizations. -/
theorem sum_pairSum_sifted (A B₁ B₂ : Finset G) (p : ℕ) (F : G → ℝ) :
    (∑ s : Fin p → G, pairSum (siftedSet A B₁ s) (siftedSet A B₂ s) F) =
      ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
        (commonShiftCount A (b₁ - b₂) : ℝ) ^ p * F (b₁ - b₂) := by
  classical
  simp only [pairSum, siftedSet, sum_filter]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b₁ hb₁
  have hpush : ∀ s : Fin p → G,
      (if ∀ i, b₁ - s i ∈ A then
          ∑ a ∈ B₂, if ∀ i, a - s i ∈ A then F (b₁ - a) else 0
        else 0) =
        ∑ a ∈ B₂, if ∀ i, b₁ - s i ∈ A then
          if ∀ i, a - s i ∈ A then F (b₁ - a) else 0 else 0 := by
    intro s
    by_cases h : ∀ i, b₁ - s i ∈ A <;> simp [h]
  simp_rw [hpush]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro b₂ hb₂
  calc
    (∑ s : Fin p → G,
      if ∀ i, b₁ - s i ∈ A then
        if ∀ i, b₂ - s i ∈ A then F (b₁ - b₂) else 0
      else 0) =
        (∑ s : Fin p → G,
          (if ∀ i, b₁ - s i ∈ A ∧ b₂ - s i ∈ A then (1 : ℝ) else 0)) *
            F (b₁ - b₂) := by
              rw [Finset.sum_mul]
              apply sum_congr rfl
              intro s hs
              split_ifs <;> simp_all
    _ = (commonShiftCount A (b₁ - b₂) : ℝ) ^ p * F (b₁ - b₂) := by
      rw [sum_all_coordinate_indicators]

section PopularDifferences

open _root_.Function _root_.MeasureTheory _root_.Real
open scoped _root_.ENNReal _root_.NNReal Indicator Pointwise

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The localized popular-differences conclusion on two finite base sets.
This is the direct finite DRC output: it records the subset relations, the
`1-δ` mass conclusion, and the exact `1/4` density constant. -/
theorem popularDifferences {A : Finset G} {p : ℕ} {ε δ : ℝ}
    (B₁ B₂ : Finset G) (hε : 0 < ε) (hε₁ : ε ≤ 1) (hδ : 0 < δ)
    (hp : Even p) (hp₂ : 2 ≤ p) (hpε : ε⁻¹ * Real.log (2 / δ) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hf : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧ x ∉ s p ε B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      1 - δ ≤ ∑ x ∈ s p ε B₁ B₂ A, (μ A₁ ○ᵈ μ A₂) x ∧
      (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
        #A₁ / #B₁ ∧
      (4 : ℝ)⁻¹ * ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) / #A ^ (2 * p) ≤
        #A₂ / #B₂ := by
  exact _root_.Erdos140.sifting B₁ B₂ hε hε₁ hδ hp hp₂ hpε hB hA hf

end PopularDifferences

end

end Sifting

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Module/AddChar.lean` -/

section
section
open _root_.AddChar
variable {R M N : Type*} [CommMonoid M] [Semiring R] [AddCommMonoid N] [Module R N]

/-- Interpret a character of the `R`-module `N` as a homomorphism from `N` to character of `R`,
via precomposition by scalar multiplication. -/
@[expose, simps]
private def _root_.AddChar.toAddMonoidHomAddChar (γ : AddChar N M) : N →+ AddChar R M where
  toFun x := {
    toFun r := γ (r • x)
    map_zero_eq_one' := by simp
    map_add_eq_mul' r s := by simp [add_smul, map_add_eq_mul]
  }
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [map_add_eq_mul, smul_add]

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Data/ZMod/Basic.lean` -/

section
section
open _root_.ZMod
variable {M : Type*} {q : ℕ}

-- FIXME: The LHS has type `Fin (q + 1)`. See
@[simp↓] private lemma _root_.ZMod.val_mk (n : ℕ) (hn) : val (n := q + 1) (⟨n, hn⟩ : ZMod (q + 1)) = n := rfl

-- FIXME: The LHS has type `Fin (q + 1)`. See
@[simp] private lemma _root_.ZMod.mk_eq_natCast (n : ℕ) (hn) : ⟨n, hn⟩ = (n : ZMod (q + 1)) :=
  (Fin.natCast_eq_mk _).symm

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Algebra/Module/ZMod.lean` -/

section
section
open _root_.AddChar
variable {R M : Type*} [Semiring R] {q : ℕ} [AddCommMonoid M] [Module (ZMod q) M] {γ : AddChar M R}
  {r : ZMod q} {x : M}

variable (γ r x) in
private lemma _root_.AddChar.map_zmod_smul [NeZero q] : γ (r • x) = γ x ^ r.val := by
  obtain _ | q := q
  · simp_all
  obtain ⟨n, hn⟩ := r
  simp [Nat.cast_smul_eq_nsmul, map_nsmul_eq_pow]

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/LinearAlgebra/Dimension/Finrank.lean` -/

section
@[expose]
private noncomputable def _root_.Submodule.finrank {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Submodule R M) : ℕ := Module.finrank R s

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean` -/

section
open scoped _root_.Finset

variable {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {s : Finset ι} {f : ι → V →ₗ[K] K}

section
open _root_.Module

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` -/

section
open scoped _root_.Finset BigOperators

section
open _root_.AddChar
variable {ι G : Type*} {q : ℕ} [AddCommGroup G]

section
variable {Δ : Set (AddChar G ℂ)} {ψ : AddChar G ℂ} {x : G}

variable [Finite G]

@[simp] private lemma _root_.AddChar.map_doubleDualEquiv_symm (χ : AddChar (AddChar G ℂ) ℂ) (ψ : AddChar G ℂ) :
    ψ (doubleDualEquiv.symm χ) = χ ψ :=
  congr($(doubleDualEmb_doubleDualEquiv_symm_apply χ) ψ)

variable {V : AddSubgroup G} [Fintype V]

end

variable [Module (ZMod q) G] {γ : AddChar G ℂ} {r : ZMod q} {x : G}

variable (q γ) in
/-- Characters of a `q`-group `G` are (noncanonically) the same as `ZMod q`-linear forms on `G`. -/
@[expose, simps! -isSimp]
private noncomputable def _root_.AddChar.toZModLinearMap [NeZero q] : G →ₗ[ZMod q] ZMod q :=
  (zmodAddEquiv.symm.toAddMonoidHom.comp <| γ.toAddMonoidHomAddChar).toZModLinearMap q

@[simp]
private lemma _root_.AddChar.toZModLinearMap_eq_zero [Fact <| 1 < q] : toZModLinearMap q γ x = 0 ↔ γ x = 1 := by
  simp +contextual only [toZModLinearMap_apply, EmbeddingLike.map_eq_zero_iff, DFunLike.ext_iff,
    toAddMonoidHomAddChar_apply_apply, map_zmod_smul, AddChar.zero_apply, iff_iff_implies_and_implies,
    one_pow, implies_true, and_true]
  rintro h
  simpa [ZMod.val_one] using h 1

@[simp]
private lemma _root_.AddChar.ker_toZModLinearMap [Fact <| 1 < q] :
    (toZModLinearMap q γ).ker = γ.toAddMonoidHom.ker.toZModSubmodule q := by ext; simp

variable [Fact q.Prime] [FiniteDimensional (ZMod q) G] {γ : ι → AddChar G ℂ}
  {s : Finset ι}

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean` -/

section
open _root_.ENNReal

section
open _root_.MeasureTheory
variable {𝕜 α : Type*} {m : MeasurableSpace α} {muWeight : Measure α} [NormedRing 𝕜]

/-- Hölder's inequality. -/
private theorem _root_.MeasureTheory.eLpNorm_mul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f g : α → 𝕜} (hf : AEStronglyMeasurable f muWeight)
    (hg : AEStronglyMeasurable g muWeight) [HolderTriple p q r] :
    eLpNorm (f * g) r muWeight ≤ eLpNorm f p muWeight * eLpNorm g q muWeight := by
  simpa using eLpNorm_smul_le_mul_eLpNorm hg hf

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Inner/Hoelder/Discrete.lean` -/

section
/-! # Inner product -/

open _root_.Finset _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped ComplexConjugate _root_.ENNReal _root_.NNReal NNRat

variable {ι 𝕜 S : Type*} [Fintype ι]

section
open _root_.RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] private lemma _root_.RCLike.wInner_one_self {_ : MeasurableSpace ι} [DiscreteMeasurableSpace ι] (f : ι → 𝕜) :
    ⟪f, f⟫_[𝕜] = ((‖f‖_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [dL2Norm_sq_eq_sum_norm, wInner_one_eq_sum]

end

/-! ### Hölder inequality -/

section
open _root_.MeasureTheory
section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0∞}
  {f g : α → ℝ}

set_option backward.isDefEq.respectTransparency false in
/-- **Hölder's inequality**, binary case. -/
private lemma _root_.MeasureTheory.wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ⟪f, g⟫_[ℝ] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  have hp0 : p ≠ 0 := ENNReal.HolderConjugate.ne_zero p q
  have hq0 : q ≠ 0 := ENNReal.HolderConjugate.ne_zero q p
  have hwInner : ⟪f, g⟫_[ℝ] = ∑ i, f i * g i := by simp [wInner_one_eq_sum, mul_comm]
  have hfg i : f i * g i ≤ ‖f i‖ * ‖g i‖ :=
    (le_abs_self _).trans_eq (by rw [abs_mul]; simp [Real.norm_eq_abs])
  obtain rfl | hpi := eq_or_ne p ∞
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).mp rfl
    simp only [hwInner, dL1Norm_eq_sum_norm, norm_eq_abs, dLinftyNorm_eq_iSup_norm, mul_sum]
    gcongr ∑ _, ?_ with i
    grw [le_abs_self (_ * _), abs_mul, ← le_ciSup (Finite.bddAbove_range _)]
  obtain rfl | hqi := eq_or_ne q ∞
  · obtain rfl : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    simp only [hwInner, dL1Norm_eq_sum_norm, norm_eq_abs, dLinftyNorm_eq_iSup_norm, sum_mul]
    gcongr ∑ _, ?_ with i
    grw [le_abs_self (_ * _), abs_mul, ← le_ciSup (Finite.bddAbove_range _)]
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpi
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hqi
  have hreal : Real.HolderConjugate p.toReal q.toReal := by
    simpa using ENNReal.HolderTriple.toReal (p := p) (q := q) (r := 1) hpr hqr
  rw [hwInner, dLpNorm_eq_sum_norm' hp0 hpi, dLpNorm_eq_sum_norm' hq0 hqi]
  simpa using Real.inner_le_Lp_mul_Lq Finset.univ f g hreal

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

set_option backward.isDefEq.respectTransparency false in
private lemma _root_.MeasureTheory.norm_wInner_one_le (f g : α → 𝕜) : ‖⟪f, g⟫_[𝕜]‖ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := by
  grw [wInner_one_eq_sum, norm_sum_le]; simp [wInner_one_eq_sum]

/-- **Hölder's inequality**, binary case. -/
private lemma _root_.MeasureTheory.norm_wInner_one_le_dLpNorm_mul_dLpNorm (p q : ℝ≥0∞) [p.HolderConjugate q] :
    ‖⟪f, g⟫_[𝕜]‖ ≤ ‖f‖_[p] * ‖g‖_[q] :=
  calc
    _ ≤ ⟪fun a ↦ ‖f a‖, fun a ↦ ‖g a‖⟫_[ℝ] := norm_wInner_one_le _ _
    _ ≤ ‖fun a ↦ ‖f a‖‖_[p] * ‖fun a ↦ ‖g a‖‖_[q] := wInner_one_le_dLpNorm_mul_dLpNorm _ _
    _ = ‖f‖_[p] * ‖g‖_[q] := by simp_rw [dLpNorm_norm .of_discrete]

omit [Fintype α]
variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
private lemma _root_.MeasureTheory.dLpNorm_mul_le (p q : ℝ≥0∞) [p.HolderTriple q r] : ‖f * g‖_[r] ≤ ‖f‖_[p] * ‖g‖_[q] := by
  cases nonempty_fintype α
  change lpNorm (f * g) r .count ≤ lpNorm f p .count * lpNorm g q .count
  have hfg : AEStronglyMeasurable (f * g) .count := .of_discrete
  grw [← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete, ← toReal_eLpNorm .of_discrete,
    ← ENNReal.toReal_mul, ← eLpNorm_mul_le_mul_eLpNorm (r := r) .of_discrete .of_discrete]
  exact (ENNReal.mul_lt_top eLpNorm_lt_top_of_finite eLpNorm_lt_top_of_finite).ne

end Hoelder
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/Inner/Hoelder/Compact.lean` -/

section
/-! # Inner product -/

open _root_.Finset hiding card
open Fintype (card)
open _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped BigOperators ComplexConjugate _root_.ENNReal _root_.NNReal NNRat

variable {ι κ 𝕜 : Type*} [Fintype ι]

section
open _root_.RCLike
variable [RCLike 𝕜] {mι : MeasurableSpace ι} [DiscreteMeasurableSpace ι] {f : ι → 𝕜}

@[simp] private lemma _root_.RCLike.wInner_cWeight_self (f : ι → 𝕜) :
    ⟪f, f⟫ₙ_[𝕜] = ((‖f‖ₙ_[2] : ℝ) : 𝕜) ^ 2 := by
  simp_rw [← algebraMap.coe_pow]
  simp [cL2Norm_sq_eq_expect_norm, wInner_cWeight_eq_expect]

end

/-! ### Hölder inequality -/

section
open _root_.MeasureTheory

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

omit [Fintype α]
variable [Finite α]

/-- **Hölder's inequality**, binary case. -/
private lemma _root_.MeasureTheory.cLpNorm_mul_le (p q : ℝ≥0∞) (_hr₀ : r ≠ 0) [hpqr : ENNReal.HolderTriple p q r] :
    ‖f * g‖ₙ_[r] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := by
  cases nonempty_fintype α
  set muWeight := ProbabilityTheory.uniformOn (Set.univ : Set α) with hmuWeight_def
  have hmuWeightfin : IsFiniteMeasure muWeight := by rw [hmuWeight_def]; infer_instance
  have hm_r : MemLp (f * g) r muWeight := MemLp.of_discrete
  have hm_p : MemLp f p muWeight := MemLp.of_discrete
  have hm_q : MemLp g q muWeight := MemLp.of_discrete
  have hbd : ∀ᵐ x ∂muWeight, ‖f x * g x‖₊ ≤ (1 : NNReal) * ‖f x‖₊ * ‖g x‖₊ :=
    .of_forall fun x ↦ by rw [one_mul]; exact nnnorm_mul_le _ _
  have key : eLpNorm (fun x ↦ f x * g x) r muWeight
      ≤ ((1 : NNReal) : ℝ≥0∞) * eLpNorm f p muWeight * eLpNorm g q muWeight :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := r)
      hm_p.aestronglyMeasurable hm_q.aestronglyMeasurable (· * ·) 1 hbd
  change lpNorm _ _ muWeight ≤ lpNorm _ _ muWeight * lpNorm _ _ muWeight
  rw [← toReal_eLpNorm hm_r.aestronglyMeasurable,
      ← toReal_eLpNorm hm_p.aestronglyMeasurable,
      ← toReal_eLpNorm hm_q.aestronglyMeasurable,
      ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.mul_ne_top hm_p.eLpNorm_ne_top hm_q.eLpNorm_ne_top
  · simpa [Pi.mul_def] using key

end Hoelder

section Real
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] {p q : ℝ≥0}
  {f g : α → ℝ}

end Real

section Hoelder
variable {α : Type*} {mα : MeasurableSpace α} [DiscreteMeasurableSpace α] [Fintype α] [RCLike 𝕜]
  {p q r : ℝ≥0∞} {f g : α → 𝕜}

omit [Fintype α] in
/-- **Hölder's inequality**, binary case. -/
private lemma _root_.MeasureTheory.cL1Norm_mul_le [Finite α] (p q : ℝ≥0∞) [hpq : ENNReal.HolderConjugate p q] :
    ‖f * g‖ₙ_[1] ≤ ‖f‖ₙ_[p] * ‖g‖ₙ_[q] := cLpNorm_mul_le _ _ one_ne_zero

end Hoelder
end

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/FourierTransform/Discrete.lean` -/

section
/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

@[expose] public section

open _root_.AddChar _root_.Finset Fintype _root_.Function _root_.MeasureTheory _root_.RCLike
open scoped BigOperators ComplexConjugate ComplexOrder _root_.ENNReal Indicator _root_.NNReal translate

variable {G : Type*} [AddCommGroup G] [Fintype G] {f : G → ℂ} {ψ : AddChar G ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
noncomputable def dft (f : G → ℂ) : AddChar G ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : G → ℂ) (ψ : AddChar G ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

/-- A special case of the **Hausdorff-Young inequality** for the discrete Fourier transform. -/
lemma norm_dft_le_dL1Norm [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ)
    (ψ : AddChar G ℂ) : ‖dft f ψ‖ ≤ ‖f‖_[1] := by
  grw [dft_apply, norm_wInner_one_le_dLpNorm_mul_dLpNorm ∞ 1, dLinftyNorm_eq_iSup_norm]
  simp [AddChar.norm_apply]

/-- A special case of the **Hausdorff-Young inequality** for the discrete Fourier transform. -/
lemma cLinftyNorm_dft_le_dL1Norm [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ) :
    ‖dft f‖ₙ_[∞] ≤ ‖f‖_[1] := by
  rw [cLpNorm_exponent_top_eq_essSup]; exact ciSup_le fun ψ ↦ norm_dft_le_dL1Norm f ψ

@[simp] lemma dft_zero : dft (0 : G → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : G → ℂ) : dft (f + g) = dft f + dft g := by
  ext; simp [wInner_add_right, dft_apply]

@[simp] lemma dft_neg (f : G → ℂ) : dft (-f) = - dft f := by ext; simp [dft_apply]

@[simp] lemma dft_sub (f g : G → ℂ) : dft (f - g) = dft f - dft g := by
  ext; simp [wInner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const G a) ψ = 0 := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply', const_apply, ← sum_mul, ← map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp]
lemma dft_smul {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 ℂ] [StarModule 𝕝 ℂ]
    [IsScalarTower 𝕝 ℂ ℂ] (c : 𝕝) (f : G → ℂ) : dft (c • f) = c • dft f := by
  ext; simp [wInner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma wInner_cWeight_dft (f g : G → ℂ) : ⟪dft f, dft g⟫ₙ_[ℂ] = ⟪f, g⟫_[ℂ] := by
  classical
  unfold dft
  simp_rw [wInner_one_eq_sum, wInner_cWeight_eq_expect, inner_apply', map_sum, map_mul,
    starRingEnd_self_apply, sum_mul, mul_sum, expect_sum_comm, mul_mul_mul_comm _ (conj <| f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul,
    AddChar.expect_apply_eq_ite, add_neg_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma cL2Norm_dft [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℂ) :
    ‖dft f‖ₙ_[2] = ‖f‖_[2] := by
  refine (sq_eq_sq₀ lpNorm_nonneg lpNorm_nonneg).1 <| Complex.ofReal_injective ?_
  push_cast
  simpa [cLpNorm, dLpNorm, RCLike.wInner_cWeight_self, wInner_one_self] using wInner_cWeight_dft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : G → ℂ) (a : G) : 𝔼 ψ, dft f ψ * ψ a = f a := by
  classical
  simp_rw [dft, wInner_one_eq_sum, inner_apply', sum_mul, expect_sum_comm, mul_right_comm _ (f _),
    ← expect_mul, ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.expect_apply_eq_ite, sub_eq_zero, boole_mul, Fintype.sum_ite_eq]

@[simp] lemma expect_dft (f : G → ℂ) : 𝔼 ψ : AddChar G ℂ, dft f ψ = f 0 := by
  simpa using dft_inversion f 0

lemma dft_dft_doubleDualEmb (f : G → ℂ) (a : G) :
    dft (dft f) (doubleDualEmb a) = card G * f (-a) := by
  simp only [← dft_inversion f (-a), dft_apply, wInner_one_eq_sum, inner_apply,
    map_neg_eq_inv, AddChar.inv_apply_eq_conj, doubleDualEmb_apply, ← Fintype.card_mul_expect,
    AddChar.card_eq]

lemma dft_dft (f : G → ℂ) : dft (dft f) = card G * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.natCast_apply, ← dft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma dft_injective : Injective (dft : (G → ℂ) → AddChar G ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (dft_inversion _ _).symm.trans <| by rw [h, dft_inversion]

@[simp]
lemma dft_conj (f : G → ℂ) (ψ : AddChar G ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, map_sum, map_mul, ← inv_apply',
    ← inv_apply_eq_conj, inv_inv, Pi.conj_apply]

lemma dft_conjneg_apply (f : G → ℂ) (ψ : AddChar G ℂ) : dft (conjneg f) ψ = conj (dft f ψ) := by
  simp only [dft_apply, wInner_one_eq_sum, inner_apply, conjneg_apply, map_sum, map_mul,
    RCLike.conj_conj]
  refine Fintype.sum_equiv (Equiv.neg G) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
lemma dft_conjneg (f : G → ℂ) : dft (conjneg f) = conj (dft f) := funext <| dft_conjneg_apply _

@[simp] lemma dft_balance (f : G → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

@[simp] lemma dft_trivChar [DecidableEq G] : dft (trivChar : G → ℂ) = 1 := by
  ext; simp [trivChar_apply, dft_apply, wInner_one_eq_sum]

@[simp] lemma dft_one : dft (1 : G → ℂ) = card G • trivChar :=
  dft_injective <| by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

@[simp] lemma dft_indicator_one_zero (A : Finset G) : dft 𝟭_[(A : Set G)] 0 = #A := by
  simp [dft_apply, wInner_one_eq_sum]

variable [DecidableEq G]

lemma dft_ddconv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) : dft (f ∗ᵈ g) ψ = dft f ψ * dft g ψ := by
  simp_rw [dft, wInner_one_eq_sum, inner_apply, ddconv_eq_sum_sub', mul_sum, sum_mul,
    ← sum_product', univ_product_univ]
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma dft_dddconv_apply (f g : G → ℂ) (ψ : AddChar G ℂ) :
    dft (f ○ᵈ g) ψ = dft f ψ * conj (dft g ψ) := by
  rw [← ddconv_conjneg, dft_ddconv_apply, dft_conjneg_apply]

@[simp]
lemma dft_ddconv (f g : G → ℂ) : dft (f ∗ᵈ g) = dft f * dft g := funext <| dft_ddconv_apply _ _

@[simp]
lemma dft_dddconv (f g : G → ℂ) : dft (f ○ᵈ g) = dft f * conj (dft g) :=
  funext <| dft_dddconv_apply _ _

@[simp] lemma dft_iterConv (f : G → ℂ) : ∀ n, dft (f ∗ᵈ^ n) = dft f ^ n
  | 0 => dft_trivChar
  | n + 1 => by simp [iterConv_succ, pow_succ, dft_iterConv]

@[simp] lemma dft_iterConv_apply (f : G → ℂ) (n : ℕ) (ψ : AddChar G ℂ) :
    dft (f ∗ᵈ^ n) ψ = dft f ψ ^ n := congr_fun (dft_iterConv _ _) _

end

/-! ### Upstream module `/tmp/apap433/APAP/Prereqs/MarcinkiewiczZygmund.lean` -/

section
/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described ∈ the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/

-- FIXME: This public import shouldn't be needed.

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality.
-/

open _root_.Finset Fintype _root_.Nat _root_.Real
variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #A ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1)
      = |∑ i, (f (a i) - (∑ b ∈ B, f (b i)) / #B)| ^ (m + 1) := by
      simp only [B, hf, sub_zero, zero_div]
    _ = |(∑ b ∈ B, ∑ i, (f (a i) - f (b i))) / #B| ^ (m + 1) := by
      simp only [sum_sub_distrib]
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      positivity
    _ = |∑ b ∈ B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / #B ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ (m + 1) := by
      gcongr; exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ m / #B := by
      rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #B := by
      gcongr; exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

lemma step_one' (hA : A.Nonempty) (f : ι → ℝ) (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) (m : ℕ)
    (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤ (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / #A ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast, Finset.card_fin,
      card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

-- works with this
-- lemma step_two_aux' {β γ : Type*} [AddCommMonoid β] [CommRing γ]
--   (f : (Fin n → ι) → (Fin n → γ)) (ε : Fin n → γ)
--   (hε : ∀ i, ε i = -1 ∨ ε i = 1) (g : (Fin n → γ) → β) :
--   ∑ a b ∈ A ^^ n, g (ε * (f a - f b)) = ∑ a b ∈ A ^^ n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)
lemma step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ) ^^ n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i, fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, mem_piFinset, ← forall_and, swapper]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only [swapper] <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  · rintro ⟨a, b⟩ _
    congr with i : 1
    simp only [mem_piFinset, mem_insert, mem_singleton] at hε
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, swapper]
    split_ifs with h
    · simp [h]
    rw [(hε i).resolve_right h]
    ring

lemma step_two (f : ι → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε ∈ ({-1, 1} : Finset ℝ)^^n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have : ∀ ε ∈ ({-1, 1} : Finset ℝ)^^n,
    ∑ a ∈ B, ∑ b ∈ B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ B, ∑ b ∈ B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl this, sum_const, card_piFinset_const, card_pair, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

lemma step_three (f : ι → ℝ) :
    ∑ ε ∈ ({-1, 1} : Finset ℝ)^^n,
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m),
          (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
            ∑ ε ∈ ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

lemma step_four {k : Fin n → ℕ} :
    ∑ ε ∈ ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  calc
    _ = ∏ i, ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ k i := by rw [← sum_prod_piFinset]
    _ = ∏ i, if Even (k i) then 2 else 0 := by
      congr with i
      split_ifs <;> simp_all [sum_pair (show (-1 : ℝ) ≠ 1 by norm_num), one_add_one_eq_two]
    _ = _ := by simp [Fintype.prod_ite_zero]

-- double_multinomial
lemma step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k ∈ piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) * ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

lemma step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

lemma step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

lemma end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
    _ ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / #A ^ n := by
      gcongr; exact step_six.trans <| step_seven.trans step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2, ← _root_.pow_succ',
        add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity

section
open _root_.Real

attribute [-instance] decidableForallFin

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly better
constant than `Real.marcinkiewicz_zygmund`. -/
private theorem _root_.Real.marcinkiewicz_zygmund' (m : ℕ) (f : ι → ℝ) (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a ∈ B, (∑ i, f (a i)) ^ (2 * m)
      ≤ ∑ a ∈ A ^^ n, (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / #A ^ n := by
      gcongr; simpa [pow_mul, sq_abs] using step_one' hA f hf (2 * m) _
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m) with ∀ i, 2 ∣ k i,
        multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [← sum_div]
      simp only [pow_mul, sq_abs]
      simp only [← pow_mul]
      rw [step_two, step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
      simp only [step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul, even_iff_two_dvd]
      rw [mul_comm, mul_div_mul_left]
      positivity
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ (piAntidiag univ m).map
          ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦ mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
        multinomial univ (fun i ↦ k i) * ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [map_nsmul_piAntidiag_univ m (ι := Fin n) (n := 2) two_ne_zero]
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
        multinomial univ (fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n := by
      simp
    _ ≤ _ := end_step hm' hA

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly easier to
bound constant than `Real.marcinkiewicz_zygmund'`.

Note that `RCLike.marcinkiewicz_zygmund` is another version that works for both `ℝ` and `ℂ` at the
expense of a slightly worse constant. -/
private theorem _root_.Real.marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → ℝ) (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) * ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1))
      ≤ (4 * ↑(m + 1)) ^ (m + 1) * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
      marcinkiewicz_zygmund' _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * (∑ a ∈ A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := ?_
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m * ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]; rfl
  gcongr with a
  rw [← div_le_iff₀' (by positivity)]
  simpa only [Finset.card_fin, pow_mul] using
    pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2) (s := univ) (fun i _ ↦ by positivity) m

end

section
open _root_.RCLike
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **Marcinkiewicz-Zygmund inequality** for real- or complex-valued functions. -/
private lemma _root_.RCLike.marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → 𝕜) (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) * ∑ a ∈ A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := re (f x)
  let f₂ x : ℝ := im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a ∈ B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a ∈ B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund hm _ hf₂
  simp only [pow_mul, RCLike.norm_sq_eq_def]
  simp only [← sq, map_sum, map_sum]
  calc
    ∑ a ∈ B, ((∑ i, re (f (a i))) ^ 2 + (∑ i, im (f (a i))) ^ 2) ^ m ≤
        ∑ a ∈ B,
          2 ^ (m - 1) * (((∑ i, re (f (a i))) ^ 2) ^ m + ((∑ i, im (f (a i))) ^ 2) ^ m) := by
      gcongr with a; apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) * (∑ a ∈ B, (∑ i, re (f (a i))) ^ (2 * m) +
          ∑ a ∈ B, (∑ i, im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i, re (f (a i)) ^ (2 * m) + (4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i, im (f (a i)) ^ (2 * m)) := by gcongr
    _ = 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i, (re (f (a i)) ^ (2 * m) + im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i, 2 * (re (f (a i)) ^ 2 + im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]; gcongr; apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) * ∑ a ∈ B, ∑ i, (re (f (a i)) ^ 2 + im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow, ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end

end

/-! ### Upstream module `/tmp/apap433/APAP/Physics/AlmostPeriodicity.lean` -/

section
/-!
# Almost-periodicity
-/

open scoped Pointwise Combinatorics.Additive Indicator translate

section
open _root_.Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}

section Add
variable [Add α]

private lemma _root_.Finset.big_shifts_step1 (L : Finset (Fin k → α)) (hk : k ≠ 0) :
    ∑ x ∈ L + s.piDiag (Fin k), ∑ l ∈ L, ∑ s ∈ s.piDiag (Fin k), (if l + s = x then 1 else 0)
      = #L * #s := by
  simp only [@sum_comm _ _ _ _ (L + _), sum_ite_eq]
  rw [sum_const_nat]
  intro l hl
  have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hk)
  rw [sum_const_nat, mul_one, Finset.card_piDiag]
  exact fun s hs ↦ if_pos (Finset.add_mem_add hl hs)

end Add

variable [AddCommGroup α] [Fintype α]

private lemma _root_.Finset.reindex_count (L : Finset (Fin k → α)) (hk : k ≠ 0) (hL' : L.Nonempty) (l₁ : Fin k → α) :
    ∑ l₂ ∈ L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 = #{t | (l₁ - fun _ ↦ t) ∈ L} :=
  calc
    _ = ∑ l₂ ∈ L, ∑ t : α, ite ((l₁ - fun _ ↦ t) = l₂) 1 0 := by
      refine sum_congr rfl fun l₂ hl₂ ↦ ?_
      rw [Fintype.sum_ite_eq_ite_exists]
      · simp only [mem_piDiag, mem_univ, eq_sub_iff_add_eq, true_and, sub_eq_iff_eq_add',
          @eq_comm _ l₁]
        rfl
      rintro i j h rfl
      cases k
      · simp at hk
      · simpa using congr_fun h 0
    _ = #{t | (l₁ - fun _ ↦ t) ∈ L} := by
      simp only [sum_comm, sum_ite_eq, card_eq_sum_ones, sum_filter]

end

section
variable {α : Type*} {g : α → ℝ} {c ε : ℝ} {A : Finset α}

open _root_.Finset
lemma my_markov (hc : 0 < c) (hg : ∀ a ∈ A, 0 ≤ g a) (h : ∑ a ∈ A, g a ≤ ε * c * #A) :
    (1 - ε) * #A ≤ #{a ∈ A | g a ≤ c} := by
  classical
  have := h.trans'
    (sum_le_sum_of_subset_of_nonneg (filter_subset (¬g · ≤ c) A) fun i hi _ ↦ hg _ hi)
  have :=
    (card_nsmul_le_sum _ _ c (by simp +contextual [le_of_lt])).trans this
  rw [nsmul_eq_mul, mul_right_comm] at this
  have := le_of_mul_le_mul_right this hc
  rw [filter_not, cast_card_sdiff (filter_subset _ _)] at this
  linarith only [this]

lemma my_other_markov (hc : 0 ≤ c) (hε : 0 ≤ ε) (hg : ∀ a ∈ A, 0 ≤ g a)
    (h : ∑ a ∈ A, g a ≤ ε * c * #A) : (1 - ε) * #A ≤ #{a ∈ A | g a ≤ c} := by
  rcases hc.lt_or_eq with (hc | rfl)
  · exact my_markov hc hg h
  simp only [mul_zero, zero_mul] at h
  classical
  rw [one_sub_mul, sub_le_comm, ← cast_card_sdiff (filter_subset _ A), ← filter_not,
    filter_false_of_mem]
  · simp only [card_empty, CharP.cast_eq_zero]; positivity
  intro i hi
  rw [(sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi]
  simp

end

open _root_.Finset _root_.Real
open scoped BigOperators Pointwise _root_.NNReal _root_.ENNReal

variable {G : Type*} [Fintype G] {A S : Finset G} {f : G → ℂ} {x ε K : ℝ} {k m : ℕ}

local notation "𝓛" x => 1 + log (min 1 x)⁻¹

private lemma curlog_pos (hx₀ : 0 < x) : 0 < 𝓛 x := by
  have : 0 ≤ log (min 1 x)⁻¹ := by bound
  positivity

section
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

open _root_.MeasureTheory in
lemma lemma28_end (hε : 0 < ε) (hm : 1 ≤ m) (hk : 64 * m / ε ^ 2 ≤ k) :
    (8 * m) ^ m * k ^ (m - 1) * #A ^ k * k * (2 * ‖f‖_[2 * m] : ℝ) ^ (2 * m) ≤
      1 / 2 * ((k * ε) ^ (2 * m) * ∑ i : G, ‖f i‖ ^ (2 * m)) * #A ^ k := by
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 2 * m ≠ 0 := by
    refine mul_ne_zero two_pos.ne' ?_
    rw [← pos_iff_ne_zero, ← Nat.succ_le_iff]
    exact hm
  rw [mul_pow (2 : ℝ), ← hmeq, ← dLpNorm_pow_eq_sum_norm hm' f, ← mul_assoc, ← mul_assoc,
    mul_right_comm _ (#A ^ k : ℝ), mul_right_comm _ (#A ^ k : ℝ),
    mul_right_comm _ (#A ^ k : ℝ)]
  rw [div_le_iff₀' (by positivity)] at hk
  gcongr ?_ * _ * _
  calc
    (8 * m : ℝ) ^ m * k ^ (m - 1) * k * 2 ^ (2 * m)
      = (8 * m) ^ m * 2 ^ (2 * m) * (k ^ (m - 1) * k) := by ring
    _ = (64 * m * k / 2) ^ m := by rw [pow_sub_one_mul (by omega), pow_mul, ← mul_pow]; ring
    _ ≤ (ε ^ 2 * k * k / 2) ^ m := by gcongr
    -- FIXME: `ring` regression. See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/ring.20regression.20in.20v4.2E19.2E0-rc2/with/511226890
    _ = (k * ε) ^ (2 * m) / 2 ^ m := by ring_nf; simp_rw [one_div]
    _ ≤ (k * ε) ^ (2 * m) / 2 ^ 1 := by gcongr; norm_num
    _ = 1 / 2 * (k * ε) ^ (2 * m) := by ring

end

variable [DecidableEq G] [AddCommGroup G]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma lemma28_part_one (hm : 1 ≤ m) (x : G) :
    ∑ a ∈ A ^^ k, ‖∑ i, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖ ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a ∈ A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) := by
  let f' : G → ℂ := fun a ↦ f (x - a) - (mu A ∗ᵈ f) x
  refine (RCLike.marcinkiewicz_zygmund (by linarith only [hm]) f' ?_).trans_eq' ?_
  · intro i
    rw [Fintype.sum_piFinset_apply, sum_sub_distrib]
    simp only [sum_const]
    rw [← Pi.smul_apply (card A), ← smul_ddconv, card_smul_mu, ddconv_eq_sum_sub']
    simp only [boole_mul, Set.indicator_apply, mem_coe]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sub_self, smul_zero]
  congr with a : 1
  simp only [sum_sub_distrib, Pi.smul_apply, sum_const, card_fin, f']

lemma big_shifts_step2 (L : Finset (Fin k → G)) (hk : k ≠ 0) :
    (∑ x ∈ L + S.piDiag (Fin k), ∑ l ∈ L, ∑ s ∈ S.piDiag (Fin k), ite (l + s = x) (1 : ℝ) 0) ^ 2
      ≤ #(L + S.piDiag (Fin k)) * #S *
        ∑ l₁ ∈ L, ∑ l₂ ∈ L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 := by
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  simp_rw [sq, sum_mul, @sum_comm _ _ _ _ (L + S.piDiag (Fin k)), boole_mul, sum_ite_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have : ∀ f : (Fin k → G) → (Fin k → G) → ℝ,
    ∑ x ∈ L, ∑ y ∈ S.piDiag (Fin k), (if x + y ∈ L + S.piDiag (Fin k) then f x y else 0) =
      ∑ x ∈ L, ∑ y ∈ S.piDiag (Fin k), f x y := by
    refine fun f ↦ sum_congr rfl fun x hx ↦ ?_
    exact sum_congr rfl fun y hy ↦ if_pos <| add_mem_add hx hy
  rw [this]
  have (x y : Fin k → G) :
      ∑ s₁ ∈ S.piDiag (Fin k), ∑ s₂ ∈ S.piDiag (Fin k), ite (y + s₂ = x + s₁) (1 : ℝ) 0 =
        ite (x - y ∈ univ.piDiag (Fin k)) 1 0 *
          ∑ s₁ ∈ S.piDiag (Fin k), ∑ s₂ ∈ S.piDiag (Fin k), ite (s₂ = x + s₁ - y) 1 0 := by
    simp_rw [mul_sum, boole_mul, ← ite_and]
    refine sum_congr rfl fun s₁ hs₁ ↦ ?_
    refine sum_congr rfl fun s₂ hs₂ ↦ ?_
    refine if_congr ?_ rfl rfl
    rw [eq_sub_iff_add_eq', and_iff_right_of_imp]
    intro h
    simp only [mem_piDiag] at hs₁ hs₂
    have : x - y = s₂ - s₁ := by rw [sub_eq_sub_iff_add_eq_add, ← h, add_comm]
    rw [this]
    obtain ⟨i, -, rfl⟩ := hs₁
    obtain ⟨j, -, rfl⟩ := hs₂
    exact mem_image.2 ⟨j - i, mem_univ _, rfl⟩
  simp_rw [@sum_comm _ _ _ _ (S.piDiag (Fin k)) L, this, sum_ite_eq']
  have : ∑ x ∈ L, ∑ y ∈ L,
        ite (x - y ∈ univ.piDiag (Fin k)) (1 : ℝ) 0 *
          ∑ z ∈ S.piDiag (Fin k), ite (x + z - y ∈ S.piDiag (Fin k)) 1 0 ≤
      ∑ x ∈ L, ∑ y ∈ L, ite (x - y ∈ univ.piDiag (Fin k)) 1 0 * (#S : ℝ) := by
    refine sum_le_sum fun l₁ _ ↦ sum_le_sum fun l₂ _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> norm_num)
    refine (sum_le_card_nsmul _ _ 1 ?_).trans_eq ?_
    · intro x _; split_ifs <;> norm_num
    have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hk)
    rw [card_piDiag]
    simp only [nsmul_one]
  refine this.trans ?_
  simp_rw [← sum_mul, mul_comm]
  rfl

-- might be true for dumb reason when k = 0, since L would be singleton and rhs is |G|,
-- so its just |S| ≤ |G|
-- Public because it is in the blueprint
public lemma big_shifts (S : Finset G) (L : Finset (Fin k → G)) (hk : k ≠ 0)
    (hL' : L.Nonempty) (hL : L ⊆ A ^^ k) :
    ∃ a : Fin k → G, a ∈ L ∧
      #L * #S ≤ #(A + S) ^ k * #{t | (a - fun _ ↦ t) ∈ L} := by
  rcases S.eq_empty_or_nonempty with (rfl | hS)
  · simpa [Finset.Nonempty, Set.Nonempty] using hL'
  have hS' : 0 < #S := by rwa [card_pos]
  have : #(L + S.piDiag _) ≤ #(A + S) ^ k := by
    refine (card_le_card (add_subset_add_right hL)).trans ?_
    rw [← Fintype.card_piFinset_const]
    refine card_le_card fun i hi ↦ ?_
    simp only [mem_add, mem_piDiag, Fintype.mem_piFinset, exists_exists_and_eq_and] at hi ⊢
    obtain ⟨y, hy, a, ha, rfl⟩ := hi
    intro j
    exact ⟨y j, hy _, a, ha, rfl⟩
  rsuffices ⟨a, ha, h⟩ : ∃ a ∈ L, #L * #S ≤ #(L + S.piDiag _) * #{t | (a - fun _ ↦ t) ∈ L}
  · exact ⟨a, ha, h.trans (Nat.mul_le_mul_right _ this)⟩
  clear! A
  have : #L ^ 2 * #S ≤
      #(L + S.piDiag _) * ∑ l₁ ∈ L, ∑ l₂ ∈ L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 := by
    refine Nat.le_of_mul_le_mul_left ?_ hS'
    rw [mul_comm, mul_assoc, ← sq, ← mul_pow, mul_left_comm, ← mul_assoc, ← big_shifts_step1 L hk]
    exact_mod_cast @big_shifts_step2 G _ _ _ _ _ L hk
  simp only [reindex_count L hk hL'] at this
  rw [sq, mul_assoc, ← smul_eq_mul, mul_sum] at this
  rw [← sum_const] at this
  exact exists_le_of_sum_le hL' this

variable [MeasurableSpace G]

namespace AlmostPeriodicity

def LProp (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : Finset G) (a : Fin k → G) : Prop :=
  ‖fun x : G ↦ ∑ i, f (x - a i) - (k • (μ A ∗ᵈ f)) x‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m]

noncomputable instance : DecidablePred (LProp k m ε f A) := Classical.decPred _

-- Public because it is in the blueprint
public noncomputable def l (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : Finset G) : Finset (Fin k → G) :=
  {x ∈ A ^^ k | LProp k m ε f A x}

lemma lemma28_markov (hε : 0 < ε) (hm : 1 ≤ m)
    (h : ∑ a ∈ A ^^ k,
        (‖fun x : G ↦ ∑ i : Fin k, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖_[2 * m] ^ (2 * m) : ℝ) ≤
      1 / 2 * (k * ε * ‖f‖_[2 * m]) ^ (2 * m) * #A ^ k) :
    (#A ^ k : ℝ) / 2 ≤ #(l k m ε f A) := by
  rw [← Nat.cast_pow, ← Fintype.card_piFinset_const] at h
  have := my_other_markov (by positivity) (by norm_num) (fun _ _ ↦ by positivity) h
  norm_num1 at this
  rw [Fintype.card_piFinset_const, mul_comm, mul_one_div, Nat.cast_pow] at this
  refine this.trans_eq ?_
  rw [l]
  congr with a : 3
  refine pow_le_pow_iff_left₀ ?_ ?_ ?_ <;> positivity

variable [DiscreteMeasurableSpace G]

open _root_.MeasureTheory in
lemma lemma28_part_two (hm : 1 ≤ m) (hA : A.Nonempty) :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ _a ∈ A ^^ k, ∑ _i : Fin k, (2 * ‖f‖_[2 * m]) ^ (2 * m) := by
  -- lots of the equalities about m can be automated but it's *way* slower
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 1 < 2 * m := (Nat.mul_le_mul_left 2 hm).trans_lt' <| by norm_num1
  have hm'' : (1 : ℝ≥0∞) ≤ 2 * m := by rw [← hmeq, Nat.one_le_cast]; exact hm'.le
  gcongr
  refine (dLpNorm_sub_le hm'').trans ?_
  rw [dLpNorm_translate, two_mul ‖f‖_[2 * m], add_le_add_iff_left]
  have hmeq' : ((2 * m : ℝ≥0) : ℝ≥0∞) = 2 * m := by
    rw [ENNReal.coe_mul, ENNReal.coe_two, ENNReal.coe_natCast]
  have : (1 : ℝ≥0) < 2 * m := by
    rw [← Nat.cast_two, ← Nat.cast_mul, Nat.one_lt_cast]
    exact hm'
  rw [← hmeq', ddconv_comm]
  refine (dLpNorm_ddconv_le this.le _ _).trans ?_
  rw [dL1Norm_mu hA, mul_one]

open _root_.MeasureTheory in
-- Public because it is in the blueprint
public lemma lemma28 (hε : 0 < ε) (hm : 1 ≤ m) (hk : (64 : ℝ) * m / ε ^ 2 ≤ k) :
    (#A ^ k : ℝ) / 2 ≤ #(l k m ε f A) := by
  have : 0 < k := by
    rw [← @Nat.cast_pos ℝ]
    refine hk.trans_lt' ?_
    refine div_pos (mul_pos (by norm_num1) ?_) (pow_pos hε _)
    rw [Nat.cast_pos, ← Nat.succ_le_iff]
    exact hm
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · simp [zero_pow this.ne']
  refine lemma28_markov hε hm ?_
  have hm' : 2 * m ≠ 0 := by linarith
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  rw [← hmeq, mul_pow]
  simp only [dLpNorm_pow_eq_sum_norm hm']
  rw [sum_comm]
  have : ∀ x : G, ∑ a ∈ A ^^ k,
      ‖∑ i, f (x - a i) - (k • (mu A ∗ᵈ f)) x‖ ^ (2 * m) ≤
    (8 * m) ^ m * k ^ (m - 1) *
      ∑ a ∈ A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) :=
    lemma28_part_one hm
  refine (sum_le_sum fun x _ ↦ this x).trans ?_
  rw [← mul_sum]
  simp only [@sum_comm _ _ G]
  have (a : Fin k → G) (i : Fin k) :
      ∑ x, ‖f (x - a i) - (mu A ∗ᵈ f) x‖ ^ (2 * m) = ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) := by
    rw [← hmeq, dLpNorm_pow_eq_sum_norm hm']
    simp only [Pi.sub_apply, translate_apply]
  simp only [this]
  have :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ᵈ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ a ∈ A ^^ k, ∑ i, (2 * ‖f‖_[2 * m]) ^ (2 * m) :=
    lemma28_part_two hm hA
  refine le_trans (mod_cast this) ?_
  simpa [mul_assoc] using lemma28_end hε hm hk

open _root_.MeasureTheory in
-- Public because it is in the blueprint
public lemma just_the_triangle_inequality {t : G} {a : Fin k → G} (ha : a ∈ l k m ε f A)
    (ha' : (a + fun _ ↦ t) ∈ l k m ε f A) (hk : 0 < k) (hm : 1 ≤ m) :
    ‖τ (-t) (mu A ∗ᵈ f) - mu A ∗ᵈ f‖_[2 * m] ≤ 2 * ε * ‖f‖_[2 * m] := by
  let f₁ : G → ℂ := fun x ↦ ∑ i, f (x - a i)
  let f₂ : G → ℂ := fun x ↦ ∑ i, f (x - a i - t)
  have hp : (1 : ℝ≥0∞) ≤ 2 * m := by norm_cast; linarith
  have h₁ : ‖f₁ - k • (mu A ∗ᵈ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rw [l, Finset.mem_filter] at ha ; exact ha.2
  have h₂ : ‖f₂ - k • (mu A ∗ᵈ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rw [l, Finset.mem_filter, LProp] at ha'
    refine ha'.2.trans_eq' ?_
    congr with i : 1
    simp [sub_sub, f₂]
  have h₃ : f₂ = τ t f₁ := by
    ext i : 1
    rw [translate_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sub_right_comm]
  have h₄₁ : ‖τ t f₁ - k • (mu A ∗ᵈ f)‖_[2 * m] = ‖τ (-t) (τ t f₁ - k • (mu A ∗ᵈ f))‖_[2 * m] := by
    rw [dLpNorm_translate]
  have h₄ : ‖τ t f₁ - k • (mu A ∗ᵈ f)‖_[2 * m] = ‖f₁ - τ (-t) (k • (mu A ∗ᵈ f))‖_[2 * m] := by
    rw [h₄₁, translate_sub_right, translate_translate]
    simp
  have h₅₁ : ‖τ (-t) (k • (mu A ∗ᵈ f)) - f₁‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rwa [dLpNorm_sub_comm, ← h₄, ← h₃]
  have : (0 : ℝ) < k := by positivity
  refine le_of_mul_le_mul_left ?_ this
  rw [← nsmul_eq_mul, ← dLpNorm_nsmul _ (_ - mu A ∗ᵈ f), nsmul_sub, ←
    translate_smul_right (-t) (mu A ∗ᵈ f) k, mul_assoc, mul_left_comm, two_mul ((k : ℝ) * _), ←
    mul_assoc]
  calc
    ‖τ (-t) (k • (μ A ∗ᵈ f)) - k • (μ A ∗ᵈ f)‖_[2 * m]
      ≤ ‖τ (-t) (k • (μ A ∗ᵈ f)) - f₁‖_[2 * m] + ‖f₁ - k • (μ A ∗ᵈ f)‖_[2 * m] :=
      dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (mod_cast hp)
    _ ≤ k * ε * ‖f‖_[2 * m] + k * ε * ‖f‖_[2 * m] := by gcongr

lemma T_bound (hK₂ : 2 ≤ K) (Lc Sc Ac ASc Tc : ℕ) (hk : k = ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊)
    (h₁ : Lc * Sc ≤ ASc ^ k * Tc) (h₂ : (Ac : ℝ) ^ k / 2 ≤ Lc) (h₃ : (ASc : ℝ) ≤ K * Ac)
    (hAc : 0 < Ac) (hε : 0 < ε) (hε' : ε ≤ 1) (hm : 1 ≤ m) :
    K ^ (-512 * m / ε ^ 2 : ℝ) * Sc ≤ Tc := by
  have hk' : k = ⌈(256 : ℝ) * m / ε ^ 2⌉₊ := by
    rw [hk, div_pow, div_div_eq_mul_div, mul_right_comm]
    congr 3
    norm_num
  have hK₀ : 0 < K := by positivity
  have : (0 : ℝ) < Ac ^ k := by positivity
  refine le_of_mul_le_mul_left ?_ this
  rw [neg_mul, neg_div, Real.rpow_neg hK₀.le, mul_left_comm, inv_mul_le_iff₀ (by positivity)]
  calc
    (Ac ^ k * Sc : ℝ)
      = 2 * (Ac ^ k / 2) * Sc := by ring
    _ ≤ K * Lc * Sc := by gcongr
    _ = K * ↑(Lc * Sc) := by push_cast; ring
    _ ≤ K * ↑(ASc ^ k * Tc) := by gcongr
    _ = K * ASc ^ k * Tc := by push_cast; ring
    _ ≤ K * (K * Ac) ^ k * Tc := by gcongr
    _ = K ^ (k + 1 : ℝ) * Ac ^ k * Tc := by norm_cast; push_cast; ring
    _ ≤ K ^ (512 * m / ε ^ 2) * Ac ^ k * Tc := ?_
    _ = K ^ (512 * m / ε ^ 2) * (Ac ^ k * Tc) := by ring
  gcongr
  · linarith
  rw [← le_sub_iff_add_le, hk', mul_div_assoc, mul_div_assoc]
  have h₄ := Nat.ceil_lt_add_one (a := 256 * (m / ε ^ 2)) (by positivity)
  have h₅ : (1 : ℝ) ≤ 128 * (m / ε ^ 2) := by rw [div_eq_mul_one_div]; bound
  linear_combination h₄ + 2 * h₅

-- trivially true for other reasons for big ε
open _root_.MeasureTheory in
-- Public because it is in the blueprint
public lemma almost_periodicity (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (m : ℕ) (f : G → ℂ)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) :
    ∃ T : Finset G,
      K ^ (-512 * m / ε ^ 2 : ℝ) * #S ≤ #T ∧
        ∀ t ∈ T, ‖τ t (mu A ∗ᵈ f) - mu A ∗ᵈ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] := by
  obtain rfl | hm := m.eq_zero_or_pos
  · exact ⟨S, by simp⟩
  obtain rfl | hA := A.eq_empty_or_nonempty
  · refine ⟨univ, ?_, fun t _ ↦ ?_⟩
    · have : K ^ ((-512 : ℝ) * m / ε ^ 2) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_two.trans hK₂) ?_
        rw [neg_mul, neg_div, Right.neg_nonpos_iff]
        positivity
      refine (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)).trans ?_
      rw [one_mul, Nat.cast_le]
      exact card_le_univ _
    simp only [mu_empty, zero_ddconv, translate_zero_right, sub_self, dLpNorm_zero]
    positivity
  let k := ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊
  have hk : k ≠ 0 := by positivity
  let L := l k m (ε / 2) f A
  have : (#A : ℝ) ^ k / 2 ≤ #L := lemma28 (half_pos hε) hm (Nat.le_ceil _)
  have hL : L.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ]
    exact this.trans_lt' (by positivity)
  obtain ⟨a, ha, hL'⟩ := big_shifts S _ hk hL (filter_subset _ _)
  refine ⟨({t | (a + fun _ ↦ -t) ∈ L} : Finset _), ?_, ?_⟩
  · simp_rw [sub_eq_add_neg] at hL'
    exact T_bound hK₂ #L #S #A #(A + S) _ rfl hL' this
      (by rw [← cast_addConst_mul_card]; gcongr) hA.card_pos hε hε' hm
  intro t ht
  simp only [mem_filter, mem_univ, true_and] at ht
  have := just_the_triangle_inequality ha ht hk.bot_lt hm
  rwa [neg_neg, mul_div_cancel₀ _ (two_ne_zero' ℝ)] at this

-- Public because it is in the blueprint
public theorem linfty_almost_periodicity (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hK₂ : 2 ≤ K)
    (hK : σ[A, S] ≤ K) (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝓛 (#C / #B)⌉ / ε ^ 2) * #S ≤ #T ∧
      ∀ t ∈ T, ‖τ t (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) - μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ ε := by
  let r : ℝ := min 1 (#C / #B)
  set m : ℝ := 𝓛 (#C / #B)
  have hm₀ : 0 < m := curlog_pos (by positivity)
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 <| by positivity
  obtain ⟨T, hKT, hT⟩ := almost_periodicity (ε / exp 1) (by positivity)
    (div_le_one_of_le₀ (hε₁.trans <| one_le_exp zero_le_one) <| by positivity) ⌈m⌉₊ (𝟭_[B]) hK₂ hK
  norm_cast at hT
  set M : ℕ := 2 * ⌈m⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by norm_cast; simp [← Nat.succ_le_iff, M]; linarith
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  have : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  refine ⟨T, ?_, fun t ht ↦ ?_⟩
  · calc
      _ = K ^(-(512 * 8) / ε ^ 2 * ⌈m⌉₊) * #S := by
          rw [mul_div_right_comm, natCast_ceil_eq_intCast_ceil hm₀.le]; norm_num
      _ ≤ K ^(-(512 * exp 1 ^ 2) / ε ^ 2 * ⌈m⌉₊) * #S := by
          gcongr
          · exact one_le_two.trans hK₂
          calc
            _ ≤ (2.7182818286 : ℝ) ^ 2 := by gcongr; exact exp_one_lt_d9.le
            _ ≤ _ := by norm_num
      _ = _ := by simp [div_div_eq_mul_div, ← mul_div_right_comm, mul_right_comm, div_pow]
      _ ≤ _ := hKT
  set F : G → ℂ := τ t (μ A ∗ᵈ 𝟭_[B]) - μ A ∗ᵈ 𝟭_[B]
  have (x : G) :=
    calc
      (τ t (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) - μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x
        = (F ∗ᵈ μ C) x := by simp [sub_ddconv, F]
      _ = ∑ y, F y * μ C (x - y) := ddconv_eq_sum_sub' ..
      _ = ∑ y, F y * μ (x +ᵥ -C) y := by simp [neg_add_eq_sub]
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ t (μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) - μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C : G → ℂ) x‖
      = ‖∑ y, F y * μ (x +ᵥ -C) y‖ := by rw [this]
    _ ≤ ∑ y, ‖F y * μ (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * μ (x +ᵥ -C)‖_[1] := by rw [MeasureTheory.dL1Norm_eq_sum_norm]; rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := MeasureTheory.dLpNorm_mul_le  _ _
    _ ≤ ε / exp 1 * #B ^ (M : ℝ)⁻¹ * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
        gcongr
        simpa [← ENNReal.coe_natCast, MeasureTheory.dLpNorm_indicator_one hM₀, F] using hT _ ht
    _ = ε * ((#C / #B) ^ (-(M : ℝ)⁻¹) / exp 1) := by
        rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
          card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc]
        any_goals positivity
        push_cast
        rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
        all_goals positivity
    _ ≤ ε := mul_le_of_le_one_right (by positivity) <| (div_le_one <| by positivity).2 ?_
  calc
    (#C / #B : ℝ) ^ (-(M : ℝ)⁻¹)
      ≤ r ^ (-(M : ℝ)⁻¹) :=
        rpow_le_rpow_of_nonpos (by positivity) inf_le_right <| neg_nonpos.2 <| by positivity
    _ ≤ r ^ (-(1 + log r⁻¹)⁻¹) :=
        rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left <| neg_le_neg <| inv_anti₀
          (by positivity) <| (Nat.le_ceil _).trans <|
            mod_cast Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ r ^ (-(0 + log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
      · simp [hr]
      have : 0 < log r⁻¹ := log_pos <| (one_lt_inv₀ (by positivity)).2 hr
      exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left (by gcongr; exact zero_le_one)
    _ = r ^ (log r)⁻¹ := by simp [inv_neg]
    _ ≤ exp 1 := rpow_inv_log_le_exp_one

public theorem linfty_almost_periodicity_boosted (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (k : ℕ)
    (hk : k ≠ 0) (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝓛 (#C / #B)⌉ * k ^ 2/ ε ^ 2) * #S ≤ #T ∧
      ‖μ T ∗ᵈ^ k ∗ᵈ (μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C) - μ A ∗ᵈ 𝟭_[B] ∗ᵈ μ C‖_[∞] ≤ ε := by
  obtain ⟨T, hKT, hT⟩ := linfty_almost_periodicity (ε / k) (by positivity)
    (div_le_one_of_le₀ (hε₁.trans <| mod_cast Nat.one_le_iff_ne_zero.2 hk) <| by positivity) hK₂ hK
    _ _ hB hC
  refine ⟨T, by simpa only [div_pow, div_div_eq_mul_div] using hKT, ?_⟩
  set F := μ_[ℂ] A ∗ᵈ 𝟭_[B] ∗ᵈ μ C
  have hT' : T.Nonempty := by
    have : (0 : ℝ) < #T := hKT.trans_lt' <| by positivity
    simpa [card_pos] using this
  calc
    (‖μ T ∗ᵈ^ k ∗ᵈ F - F‖_[∞] : ℝ)
      = ‖𝔼 a ∈ T ^^ k, (τ (∑ i, a i) F - F)‖_[∞] := by
        rw [mu_iterConv_ddconv, expect_sub_distrib, expect_const hT'.piFinset_const]
    _ ≤ 𝔼 a ∈ T ^^ k, ‖τ (∑ i, a i) F - F‖_[∞] := MeasureTheory.dLpNorm_expect_le le_top
    _ ≤ 𝔼 _a ∈ T ^^ k, ε := ?_
    _ = ε := by rw [expect_const hT'.piFinset_const]
  refine expect_le_expect fun x hx ↦
  calc
    (‖τ (∑ i, x i) F - F‖_[⊤] : ℝ)
    _ ≤ ∑ i, ‖τ (x i) F - F‖_[⊤] := MeasureTheory.dLpNorm_translate_sum_sub_le le_top _ _ _
    _ ≤ ∑ _i, ε / k := by gcongr; exact hT _ <| Fintype.mem_piFinset.1 hx _
    _ = ε := by simp only [sum_const, card_fin, nsmul_eq_mul]; rw [mul_div_cancel₀]; positivity

end AlmostPeriodicity

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/MarcinkiewiczZygmund.lean` -/

section
/-!
# A finite Marcinkiewicz--Zygmund inequality

This file proves the even-moment estimate used by the Croot--Sisask sampling
argument.  Everything is an ordinary finite sum: `A ^^ n` is the set of
`n`-tuples with entries in `A`, equipped with counting measure.  Thus no
measure-theoretic independence infrastructure is needed.

The final result, `RCLike.marcinkiewicz_zygmund_v1`, applies to real- or
complex-valued functions of mean zero.  Its deliberately coarse explicit
constant is

`(8 * m) ^ m * n ^ (m - 1)`

for the moment `2 * m`.  This is the form needed after centering the samples
in the proof of almost-periodicity.
-/

open _root_.Finset Fintype _root_.Nat

variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

private lemma mz_step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #A ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1)
        = |∑ i, (f (a i) - (∑ b ∈ B, f (b i)) / #B)| ^ (m + 1) := by
          simp only [B, hf, sub_zero, zero_div]
    _ = |(∑ b ∈ B, ∑ i, (f (a i) - f (b i))) / #B| ^ (m + 1) := by
          simp only [sum_sub_distrib]
          rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset,
            prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
            mul_div_cancel_left₀]
          positivity
    _ = |∑ b ∈ B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / #B ^ (m + 1) := by
          rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ (m + 1) := by
          gcongr
          exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b ∈ B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / #B ^ m / #B := by
          rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / #B := by
          gcongr
          exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

private lemma mz_step_one' (hA : A.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) (m : ℕ) (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤
      (∑ b ∈ A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / #A ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast,
      Finset.card_fin, card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  · exact mz_step_one hA f a hf

private lemma mz_step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ) ^^ n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i,
      fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, mem_piFinset, ← forall_and, swapper]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only [swapper] <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  rintro ⟨a, b⟩ _
  congr with i : 1
  simp only [mem_piFinset, mem_insert, mem_singleton] at hε
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, swapper]
  split_ifs with h
  · simp [h]
  rw [(hε i).resolve_right h]
  ring

private lemma mz_step_two (f : ι → ℝ) :
    ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have h : ∀ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
      ∑ a ∈ B, ∑ b ∈ B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
        ∑ a ∈ B, ∑ b ∈ B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ mz_step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl h, sum_const, card_piFinset_const, card_pair,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

private lemma mz_step_three (f : ι → ℝ) :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n,
        ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ (2 * m),
        (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
          ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ),
    ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

private lemma mz_step_four {k : Fin n → ℕ} :
    ∑ ε ∈ ({-1, 1} : Finset ℝ) ^^ n, ∏ t, ε t ^ k t =
      2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  calc
    _ = ∏ i, ∑ j ∈ ({-1, 1} : Finset ℝ), j ^ k i := by
          rw [← sum_prod_piFinset]
    _ = ∏ i, if Even (k i) then 2 else 0 := by
          congr with i
          split_ifs <;>
            simp_all [sum_pair (show (-1 : ℝ) ≠ 1 by norm_num), one_add_one_eq_two]
    _ = _ := by simp [Fintype.prod_ite_zero]

private lemma mz_step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k ∈ piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) *
          ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  refine sum_le_sum fun k hk ↦ ?_
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

private lemma mz_step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

private lemma mz_step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

private lemma mz_end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a ∈ B, ∑ b ∈ B, ∑ k ∈ piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) *
        ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n
        ≤ (∑ a ∈ B, ∑ b ∈ B, m ^ m * 2 ^ (m + (m - 1)) *
            ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) /
            #A ^ n := by
          gcongr
          exact mz_step_six.trans <| mz_step_seven.trans mz_step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2,
        ← _root_.pow_succ', add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow,
        ← mul_pow, card_piFinset, prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_pow, mul_div_cancel_left₀]
      · norm_num
        dsimp [B]
      · positivity

section
open _root_.Real

attribute [-instance] decidableForallFin

/-- The finite Marcinkiewicz--Zygmund inequality in its square-function form.
The `n` coordinate samples are independent because the sum ranges over the
entire product `A ^^ n`. -/
private theorem _root_.Real.marcinkiewicz_zygmund_square (m : ℕ) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a ∈ B, (∑ i, f (a i)) ^ (2 * m)
        ≤ ∑ a ∈ A ^^ n,
            (∑ b ∈ B, |∑ i, (f (a i) - f (b i))| ^ (2 * m)) / #A ^ n := by
          gcongr
          simpa [pow_mul, sq_abs] using mz_step_one' hA f hf (2 * m) _
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          ∑ k ∈ piAntidiag univ (2 * m) with ∀ i, 2 ∣ k i,
            multinomial univ (fun i ↦ k i) *
              ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [← sum_div]
      simp only [pow_mul, sq_abs]
      simp only [← pow_mul]
      rw [mz_step_two, mz_step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
      simp only [mz_step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul,
        even_iff_two_dvd]
      rw [mul_comm, mul_div_mul_left]
      positivity
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n,
          ∑ k ∈ (piAntidiag univ m).map
            ⟨(2 • ·), fun _ _ h ↦ funext fun i ↦
              mul_right_injective₀ two_ne_zero (congr_fun h i)⟩,
            multinomial univ (fun i ↦ k i) *
              ∏ t, (f (a t) - f (b t)) ^ k t) / #A ^ n := by
      rw [map_nsmul_piAntidiag_univ m (ι := Fin n) (n := 2) two_ne_zero]
    _ = (∑ a ∈ A ^^ n, ∑ b ∈ A ^^ n, ∑ k ∈ piAntidiag univ m,
          multinomial univ (fun i ↦ 2 * k i) *
            ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / #A ^ n := by
      simp
    _ ≤ _ := mz_end_step hm' hA

/-- A one-sum version of finite Marcinkiewicz--Zygmund for real functions.
Compared with the square-function form, Hölder costs `n^(m-1)`. -/
private theorem _root_.Real.marcinkiewicz_zygmund_v1 (hm : m ≠ 0) (f : ι → ℝ)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a ∈ A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1))
        ≤ (4 * ↑(m + 1)) ^ (m + 1) *
            ∑ a ∈ A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
          marcinkiewicz_zygmund_square _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) *
          (∑ a ∈ A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := by
      gcongr with a
      rw [← div_le_iff₀' (by positivity)]
      simpa only [Finset.card_fin, pow_mul] using
        pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2) (s := univ)
          (fun i _ ↦ by positivity) m
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m *
          ∑ a ∈ A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]
      rfl

end

section
open _root_.RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The finite Marcinkiewicz--Zygmund inequality for real- or complex-valued
mean-zero samples.  This is the form directly used by Croot--Sisask. -/
private theorem _root_.RCLike.marcinkiewicz_zygmund_v1 (hm : m ≠ 0) (f : ι → 𝕜)
    (hf : ∀ i, ∑ a ∈ A ^^ n, f (a i) = 0) :
    ∑ a ∈ A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := _root_.RCLike.re (f x)
  let f₂ x : ℝ := _root_.RCLike.im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a ∈ B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a ∈ B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund_v1 hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund_v1 hm _ hf₂
  simp only [pow_mul, _root_.RCLike.norm_sq_eq_def]
  simp only [← sq, map_sum, map_sum]
  calc
    ∑ a ∈ B,
        ((∑ i, _root_.RCLike.re (f (a i))) ^ 2 +
          (∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m ≤
      ∑ a ∈ B, 2 ^ (m - 1) *
        (((∑ i, _root_.RCLike.re (f (a i))) ^ 2) ^ m +
          ((∑ i, _root_.RCLike.im (f (a i))) ^ 2) ^ m) := by
          gcongr with a
          apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) *
        (∑ a ∈ B, (∑ i, _root_.RCLike.re (f (a i))) ^ (2 * m) +
          ∑ a ∈ B, (∑ i, _root_.RCLike.im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.re (f (a i)) ^ (2 * m) +
          (4 * m) ^ m * n ^ (m - 1) *
            ∑ a ∈ B, ∑ i, _root_.RCLike.im (f (a i)) ^ (2 * m)) := by
      gcongr
    _ = 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i,
            (_root_.RCLike.re (f (a i)) ^ (2 * m) +
              _root_.RCLike.im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) *
        ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a ∈ B, ∑ i,
            2 * (_root_.RCLike.re (f (a i)) ^ 2 +
              _root_.RCLike.im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]
      gcongr
      apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) *
        ∑ a ∈ B, ∑ i,
          (_root_.RCLike.re (f (a i)) ^ 2 +
            _root_.RCLike.im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow,
        ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/CrootSisask.lean` -/

section
/-!
# Croot--Sisask almost-periodicity for Erdős Problem 140

This module records the exact finite Croot--Sisask theorem used in the
localized Bloom--Sisask argument. The underlying proof is the fully
formalized finite sampling argument in `APAP.Physics.AlmostPeriodicity`.
It supplies the finite MZ sampling estimate, retains half the samples, and
uses the large-fibre lemma to obtain the explicit `K ^ (-512 m / ε²)` loss.

Only the sound finite almost-periodicity module is imported. In particular,
this file does not import APAP's unfinished integer Roth theorem or its
unfinished regular-Bohr-set module.
-/

open _root_.Finset
open scoped BigOperators Pointwise translate Indicator _root_.ENNReal _root_.NNReal

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

noncomputable def crootSisaskSampleSize (q : ℕ) (ε : ℝ) : ℕ :=
  ⌈(64 : ℝ) * q / (ε / 2) ^ 2⌉₊

/-- The standard subset form of Croot--Sisask. Every element of `T - T` is
an almost period, and the exact sampling/pigeonhole density is retained. -/
theorem croot_sisask_subset
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (q : ℕ) (hq : 1 ≤ q) (ε : ℝ) (hε : 0 < ε) (f : G → ℂ) :
    let k := crootSisaskSampleSize q ε
    ∃ T : Finset G,
      T ⊆ S ∧
      T.Nonempty ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ‖τ (t - s) (mu A ∗ᵈ f) - mu A ∗ᵈ f‖_[2 * q] ≤
          ε * ‖f‖_[2 * q] := by
  classical
  let k := crootSisaskSampleSize q ε
  let L := AlmostPeriodicity.l k q (ε / 2) f A
  have hkLower : (64 : ℝ) * q / (ε / 2) ^ 2 ≤ k := by
    change (64 : ℝ) * q / (ε / 2) ^ 2 ≤
      (↑⌈(64 : ℝ) * q / (ε / 2) ^ 2⌉₊ : ℝ)
    exact Nat.le_ceil _
  have hkpos : 0 < k := by
    rw [← @Nat.cast_pos ℝ]
    exact hkLower.trans_lt'
      (div_pos (mul_pos (by norm_num) (by positivity)) (pow_pos (half_pos hε) 2))
  have hLcard : (#A : ℝ) ^ k / 2 ≤ #L :=
    AlmostPeriodicity.lemma28 (half_pos hε) hq hkLower
  have hLne : L.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ]
    exact hLcard.trans_lt' (by positivity)
  let P : Finset ((Fin k → G) × G) := L ×ˢ S
  let X : Finset (Fin k → G) := (A + S) ^^ k
  let φ : ((Fin k → G) × G) → (Fin k → G) := fun z ↦ z.1 + fun _ ↦ z.2
  have hXne : X.Nonempty := (hA.add hS).piFinset_const
  have hmap : ∀ z ∈ P, φ z ∈ X := by
    rintro ⟨l, s⟩ hls
    simp only [P, mem_product] at hls
    simp only [X, Fintype.mem_piFinset, φ, Pi.add_apply]
    have hlGood : l ∈ L := hls.1
    change l ∈ AlmostPeriodicity.l k q (ε / 2) f A at hlGood
    rw [AlmostPeriodicity.l, mem_filter] at hlGood
    have hl : l ∈ A ^^ k := hlGood.1
    intro i
    exact Finset.add_mem_add (Fintype.mem_piFinset.1 hl i) hls.2
  have hXcard : #X = #(A + S) ^ k := by simp [X]
  have hXcardR : (#X : ℝ) = (#(A + S) : ℝ) ^ k := by
    rw [hXcard]
    norm_cast
  have hXcardNe : (#X : ℝ) ≠ 0 := by exact_mod_cast hXne.card_ne_zero
  have hpigeon :
      ∃ x ∈ X, ((#L : ℝ) * #S) / #X ≤
        ∑ z ∈ P with φ z = x, (1 : ℝ) := by
    refine Finset.exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hmap hXne ?_
    simp only [nsmul_eq_mul, sum_const, P, card_product, Nat.cast_mul]
    rw [mul_comm (#X : ℝ), div_mul_cancel₀ _ hXcardNe, mul_one]
  obtain ⟨x, hxX, hx⟩ := hpigeon
  let Q : Finset ((Fin k → G) × G) := {z ∈ P | φ z = x}
  let T : Finset G := Q.image Prod.snd
  have hQcard : (#Q : ℝ) = ∑ z ∈ P with φ z = x, (1 : ℝ) := by simp [Q]
  have hsndInj : Set.InjOn Prod.snd (Q : Set ((Fin k → G) × G)) := by
    rintro ⟨l₁, s₁⟩ hz₁ ⟨l₂, s₂⟩ hz₂ hs
    have hz₁' : (l₁, s₁) ∈ Q := hz₁
    have hz₂' : (l₂, s₂) ∈ Q := hz₂
    have hφ : l₁ + (fun _ ↦ s₁) = l₂ + fun _ ↦ s₂ :=
      (mem_filter.1 hz₁').2.trans (mem_filter.1 hz₂').2.symm
    cases hs
    apply Prod.ext
    · funext i
      exact add_right_cancel (congr_fun hφ i)
    · rfl
  have hTcard : #T = #Q := card_image_iff.mpr hsndInj
  have hQpos : (0 : ℝ) < #Q := by
    have hratioPos : 0 < ((#L : ℝ) * #S) / #X :=
      div_pos (mul_pos (by exact_mod_cast hLne.card_pos) (by exact_mod_cast hS.card_pos))
        (by exact_mod_cast hXne.card_pos)
    exact hratioPos.trans_le (by simpa [hQcard] using hx)
  have hTne : T.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ, hTcard]
    exact hQpos
  refine ⟨T, ?_, hTne, ?_, ?_⟩
  · intro s hsT
    obtain ⟨z, hzQ, rfl⟩ := mem_image.1 hsT
    exact (mem_product.1 (mem_filter.1 hzQ).1).2
  · calc
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k)
          = (((#A : ℝ) ^ k / 2 * #S) / #X) := by rw [hXcardR]
      _ ≤ ((#L : ℝ) * #S) / #X := by gcongr
      _ ≤ #Q := by simpa [hQcard] using hx
      _ = #T := by exact_mod_cast hTcard.symm
  · intro s hsT t htT
    obtain ⟨⟨a, s'⟩, hasQ, hs'⟩ := mem_image.1 hsT
    obtain ⟨⟨b, t'⟩, hbtQ, ht'⟩ := mem_image.1 htT
    simp only at hs' ht'
    subst s'
    subst t'
    have has : a ∈ L := (mem_product.1 (mem_filter.1 hasQ).1).1
    have hbt : b ∈ L := (mem_product.1 (mem_filter.1 hbtQ).1).1
    have hax : a + (fun _ ↦ s) = x := (mem_filter.1 hasQ).2
    have hbx : b + (fun _ ↦ t) = x := (mem_filter.1 hbtQ).2
    have hab : a + (fun _ ↦ s - t) = b := by
      funext i
      have ha := congr_fun hax i
      have hb := congr_fun hbx i
      simp only [Pi.add_apply] at ha hb ⊢
      calc
        a i + (s - t) = (a i + s) - t := by abel
        _ = x i - t := by rw [ha]
        _ = b i := by rw [← hb]; abel
    have habGood : a + (fun _ ↦ s - t) ∈ L := by rw [hab]; exact hbt
    have htri := AlmostPeriodicity.just_the_triangle_inequality
      (A := A) (f := f) (m := q) (k := k) (t := s - t) has habGood hkpos hq
    simpa [neg_sub, mul_div_cancel₀ _ (two_ne_zero' ℝ)] using htri

private theorem crootSisaskRatioBound
    {G : Type*} [Fintype G] (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty)
    (q : ℕ) (hq : q = ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊) :
    ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) ≤ Real.exp 1 := by
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hden : 0 < 1 + Real.log r⁻¹ := by
    have hloginv : 0 ≤ Real.log r⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    linarith
  have hq₁ : 1 ≤ q := by
    rw [hq, Nat.one_le_ceil_iff]
    have hloginv : 0 ≤ Real.log r⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    dsimp [r] at hloginv ⊢
    linarith
  calc
    ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹)
        ≤ r ^ (-((2 * q : ℕ) : ℝ)⁻¹) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) inf_le_right <| neg_nonpos.2 <| by positivity
    _ ≤ r ^ (-(1 + Real.log r⁻¹)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) hrle <| neg_le_neg <| inv_anti₀
        hden <| (Nat.le_ceil _).trans <| by
          rw [← hq]
          exact_mod_cast Nat.le_mul_of_pos_left q (by norm_num : 0 < 2)
    _ ≤ r ^ (-(0 + Real.log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := hrle.eq_or_lt
      · simp [hr]
      have : 0 < Real.log r⁻¹ := Real.log_pos <| (one_lt_inv₀ hrpos).2 hr
      exact Real.rpow_le_rpow_of_exponent_ge (by positivity) hrle
        (by gcongr; exact zero_le_one)
    _ = r ^ (Real.log r)⁻¹ := by simp [inv_neg]
    _ ≤ Real.exp 1 := Real.rpow_inv_log_le_exp_one

private theorem crootSisaskHolderNormAt
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} (B C : Finset G) (u x : G) (q : ℕ) (hq₁ : 1 ≤ q) :
    ‖(τ u ((mu A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖ ≤
        ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[2 * q] *
          ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent (2 * q)] := by
  let M : ℕ := 2 * q
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    dsimp [M]
    omega
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  have hM' : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  set F : G → ℂ := τ u (mu A ∗ᵈ 𝟭_[B]) - mu A ∗ᵈ 𝟭_[B]
  have hconv :
      (τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x =
        (F ∗ᵈ mu C) x := by simp [sub_ddconv, F]
  have hsum : (F ∗ᵈ mu C) x = ∑ y, F y * mu (x +ᵥ -C) y := by
    rw [ddconv_eq_sum_sub']
    congr with y
    simp [neg_add_eq_sub]
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        = ‖∑ y, F y * mu (x +ᵥ -C) y‖ := by rw [hconv, hsum]
    _ ≤ ∑ y, ‖F y * mu (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * mu (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ = _ := by simp [F, M]

private theorem crootSisaskHolderAt
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} {ε : ℝ} (B C : Finset G)
    (hC : C.Nonempty) (u x : G) (q : ℕ) (hq₁ : 1 ≤ q)
    (hF₀ :
      ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[
          2 * q] ≤
        ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[
          2 * q]) :
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖ ≤
        ε * (((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) / Real.exp 1) := by
  let M : ℕ := 2 * q
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    dsimp [M]
    omega
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        ≤ ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[M] *
            ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
          simpa [M] using crootSisaskHolderNormAt B C u x q hq₁
    _ ≤ ε / Real.exp 1 * #B ^ (M : ℝ)⁻¹ *
          ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      have hF₁ :
          ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[M] ≤
            ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[M] := by
        simpa only [M, Nat.cast_mul, Nat.cast_ofNat] using hF₀
      have hind : ‖(𝟭_[B] : G → ℂ)‖_[M] = (#B : ℝ) ^ (M : ℝ)⁻¹ := by
        rw [show (M : ℝ≥0∞) = ((M : ℝ≥0) : ℝ≥0∞) by norm_num,
          MeasureTheory.dLpNorm_indicator_one hM₀]
        norm_num
      rw [← hind]
      exact hF₁
    _ = ε * (((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹) / Real.exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, Real.div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [Real.rpow_neg, Real.rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ = ε * (((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) / Real.exp 1) := by
      simp [M]

private theorem crootSisaskHolderUpgrade
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} {ε : ℝ} (hε : 0 < ε) (B C : Finset G)
    (hC : C.Nonempty) (u : G) (q : ℕ) (hq₁ : 1 ≤ q)
    (hratio : ((#C : ℝ) / #B) ^ (-((2 * q : ℕ) : ℝ)⁻¹) ≤ Real.exp 1)
    (hF₀ :
      ‖τ u (mu A ∗ᵈ (𝟭_[B] : G → ℂ)) - mu A ∗ᵈ 𝟭_[B]‖_[
          2 * q] ≤
        ε / Real.exp 1 * ‖(𝟭_[B] : G → ℂ)‖_[
          2 * q]) :
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
      (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ (crootSisaskHolderAt B C hC u x q hq₁ hF₀).trans ?_
  refine mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 ?_)
  exact hratio

/-- Three-factor `L^∞` Croot--Sisask while retaining `T ⊆ S`.
Every difference of two elements of `T` is an `L^∞` almost period. -/
theorem croot_sisask_linfty_subset
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    let q := ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊
    let k := crootSisaskSampleSize q (ε / Real.exp 1)
    ∃ T : Finset G,
      T ⊆ S ∧ T.Nonempty ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ∀ s ∈ T, ∀ t ∈ T,
        ‖(τ (t - s) ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
          (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  let m : ℝ := 1 + Real.log r⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hm₀ : 0 < m := by
    have : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    positivity
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hTS, hTne, hcard, hT⟩ :=
    croot_sisask_subset hA hS ⌈m⌉₊ hm₁ (ε / Real.exp 1) (by positivity)
      (𝟭_[B] : G → ℂ)
  refine ⟨T, hTS, hTne, ?_, ?_⟩
  · simpa [r, m] using hcard
  · intro s hs t ht
    apply crootSisaskHolderUpgrade hε B C hC (t - s) ⌈m⌉₊ hm₁
      (crootSisaskRatioBound B C hB hC ⌈m⌉₊ (by simp [r, m]))
    simpa [r, m] using hT s hs t ht
  /-
  let r : ℝ := min 1 ((#C : ℝ) / #B)
  let m : ℝ := 1 + Real.log r⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min one_pos (div_pos (by exact_mod_cast hC.card_pos) (by exact_mod_cast hB.card_pos))
  have hrle : r ≤ 1 := min_le_left _ _
  have hm₀ : 0 < m := by
    have : 0 ≤ Real.log r⁻¹ := Real.log_nonneg ((one_le_inv₀ hrpos).2 hrle)
    positivity
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 (by positivity)
  obtain ⟨T, hTS, hTne, hcard, hT⟩ :=
    croot_sisask_subset hA hS ⌈m⌉₊ hm₁ (ε / Real.exp 1) (by positivity)
      (𝟭_[B] : G → ℂ)
  norm_cast at hT
  let M : ℕ := 2 * ⌈m⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by
    norm_cast
    simp [← Nat.succ_le_iff, M]
    linarith
  have hM : (M : ℝ≥0).HolderConjugate _ := NNReal.HolderConjugate.conjExponent hM₁
  have hM' : (M : ℝ≥0∞).HolderConjugate _ := hM.coe_ennreal
  refine ⟨T, hTS, hTne, hcard, ?_⟩
  intro s hs t ht
  let u : G := t - s
  set F : G → ℂ := τ u (mu A ∗ᵈ 𝟭_[B]) - mu A ∗ᵈ 𝟭_[B]
  have hconv (x : G) :
      (τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x =
        (F ∗ᵈ mu C) x := by simp [sub_ddconv, F]
  have hsum (x : G) : (F ∗ᵈ mu C) x = ∑ y, F y * mu (x +ᵥ -C) y := by
    rw [ddconv_eq_sum_sub']
    congr with y
    simp [neg_add_eq_sub]
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ u ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) - (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ) x‖
        = ‖∑ y, F y * mu (x +ᵥ -C) y‖ := by rw [hconv, hsum]
    _ ≤ ∑ y, ‖F y * mu (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * mu (x +ᵥ -C)‖_[1] := by
      rw [MeasureTheory.dL1Norm_eq_sum_norm]
      rfl
    _ ≤ ‖F‖_[M] * ‖mu_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] :=
      MeasureTheory.dLpNorm_mul_le _ _
    _ ≤ ε / Real.exp 1 * #B ^ (M : ℝ)⁻¹ *
          ‖mu_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
      gcongr
      simpa [← ENNReal.coe_natCast, MeasureTheory.dLpNorm_indicator_one hM₀, F, u, M]
        using hT s hs t ht
    _ = ε * (((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹) / Real.exp 1) := by
      rw [← mul_comm_div, MeasureTheory.dLpNorm_mu hM.symm.lt.le hC.neg.vadd_finset,
        card_vadd_finset, card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc]
      any_goals positivity
      push_cast
      rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
      all_goals positivity
    _ ≤ ε := mul_le_of_le_one_right (by positivity) <| (div_le_one <| by positivity).2 ?_
  calc
    ((#C : ℝ) / #B) ^ (-(M : ℝ)⁻¹)
        ≤ r ^ (-(M : ℝ)⁻¹) :=
      rpow_le_rpow_of_nonpos (by positivity) inf_le_right <| neg_nonpos.2 <| by positivity
    _ ≤ r ^ (-(1 + Real.log r⁻¹)⁻¹) :=
      rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left <| neg_le_neg <| inv_anti₀
        (by positivity) <| (Nat.le_ceil _).trans <| mod_cast Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ r ^ (-(0 + Real.log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
      · simp [hr]
      have : 0 < Real.log r⁻¹ := Real.log_pos <| (one_lt_inv₀ (by positivity)).2 hr
      exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left (by gcongr; exact zero_le_one)
    _ = r ^ (Real.log r)⁻¹ := by simp [inv_neg]
    _ ≤ Real.exp 1 := rpow_inv_log_le_exp_one
  -/

/-- Boosted subset-preserving `L^∞` almost-periodicity. The large set `T`
remains a subset of `S`; recentering it at `z ∈ T` makes zero an element of
the averaging set. -/
theorem croot_sisask_linfty_subset_boosted
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : m ≠ 0)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    let q := ⌈1 + Real.log (min 1 ((#C : ℝ) / #B))⁻¹⌉₊
    let k := crootSisaskSampleSize q ((ε / m) / Real.exp 1)
    ∃ (T : Finset G) (z : G),
      T ⊆ S ∧ z ∈ T ∧
      (-z +ᵥ T).Nonempty ∧ (-z +ᵥ T) ⊆ S - S ∧
      (((#A : ℝ) ^ k / 2 * #S) / (#(A + S) : ℝ) ^ k ≤ #T) ∧
      ‖(mu (-z +ᵥ T) ∗ᵈ^ m ∗ᵈ ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_iff_ne_zero.2 hm)
  have hδ : 0 < ε / (m : ℝ) := div_pos hε hmpos
  obtain ⟨T, hTS, hTne, hcard, hperiod⟩ :=
    croot_sisask_linfty_subset hA hS (ε / (m : ℝ)) hδ B C hB hC
  obtain ⟨z, hz⟩ := hTne
  let X : Finset G := -z +ᵥ T
  have hXne : X.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ -z +ᵥ T
    rw [mem_vadd_finset]
    exact ⟨z, hz, by simp⟩
  have hXperiod : ∀ x ∈ X,
      ‖(τ x ((mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C) -
        (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C : G → ℂ)‖_[∞] ≤ ε / (m : ℝ) := by
    intro x hx
    change x ∈ -z +ᵥ T at hx
    rw [mem_vadd_finset] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hp := hperiod z hz t ht
    simpa [sub_eq_add_neg, add_comm] using hp
  have hXsub : -z +ᵥ T ⊆ S - S := by
    intro x hx
    rw [mem_vadd_finset] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simpa [sub_eq_add_neg, add_comm] using sub_mem_sub (hTS ht) (hTS hz)
  set F : G → ℂ := (mu A ∗ᵈ 𝟭_[B]) ∗ᵈ mu C
  refine ⟨T, z, hTS, hz, ?_, hXsub, ?_, ?_⟩
  · simpa [X] using hXne
  · simpa using hcard
  · change ‖mu X ∗ᵈ^ m ∗ᵈ F - F‖_[∞] ≤ ε
    calc
      (‖mu X ∗ᵈ^ m ∗ᵈ F - F‖_[∞] : ℝ)
          = ‖𝔼 a ∈ X ^^ m, (τ (∑ i, a i) F - F)‖_[∞] := by
            rw [mu_iterConv_ddconv, expect_sub_distrib, expect_const hXne.piFinset_const]
      _ ≤ 𝔼 a ∈ X ^^ m, ‖τ (∑ i, a i) F - F‖_[∞] :=
        MeasureTheory.dLpNorm_expect_le le_top
      _ ≤ 𝔼 _a ∈ X ^^ m, ε := by
        refine expect_le_expect fun a ha ↦ ?_
        calc
          (‖τ (∑ i, a i) F - F‖_[∞] : ℝ)
              ≤ ∑ i, ‖τ (a i) F - F‖_[∞] :=
                MeasureTheory.dLpNorm_translate_sum_sub_le le_top _ _ _
          _ ≤ ∑ _i, ε / (m : ℝ) := by
            gcongr
            simpa [F] using hXperiod (a _) (Fintype.mem_piFinset.1 ha _)
          _ = ε := by
            simp only [sum_const, card_fin, nsmul_eq_mul]
            rw [mul_div_cancel₀]
            exact_mod_cast hm
      _ = ε := by rw [expect_const hXne.piFinset_const]

/-- Finite Croot--Sisask almost-periodicity with an explicit large-set bound.
The exponent `2 * m` is the even moment furnished by the sampling proof. -/
alias croot_sisask := AlmostPeriodicity.almost_periodicity
/-- The three-factor `L^∞` consequence of Croot--Sisask obtained by Hölder. -/
alias croot_sisask_linfty := AlmostPeriodicity.linfty_almost_periodicity
/-- The boosted three-factor form, in which averaging over `k`-fold sums of
almost periods changes the convolution by at most `ε` in `L^∞`. -/
alias croot_sisask_linfty_boosted :=
  AlmostPeriodicity.linfty_almost_periodicity_boosted

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/FiniteFourier.lean` -/

section
/-!
# Normalized Fourier analysis on a finite abelian group

This file contains the elementary finite Fourier identities used in the proof of
Erdős Problem 140.  Both the Fourier transform and convolution are normalized
with respect to the uniform probability measure on the ambient group.
-/

noncomputable section

open _root_.AddChar _root_.Finset Fintype _root_.Function _root_.RCLike
open scoped BigOperators ComplexConjugate

namespace FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized Fourier coefficient
`E_x conj (χ x) * f x` of a complex-valued function on a finite abelian group. -/
def coeff (f : G → ℂ) (χ : AddChar G ℂ) : ℂ := ⟪(χ : G → ℂ), f⟫ₙ_[ℂ]

@[simp] lemma coeff_zero (χ : AddChar G ℂ) : coeff (0 : G → ℂ) χ = 0 := by
  simp [coeff]

/-- Fourier inversion, with normalized coefficients and an unnormalized sum over the dual. -/
lemma inversion (f : G → ℂ) (a : G) :
    ∑ χ : AddChar G ℂ, coeff f χ * χ a = f a := by
  classical
  simp_rw [coeff, wInner_cWeight_eq_expect, inner_apply', expect_mul,
    ← expect_sum_comm, mul_right_comm _ (f _), ← sum_mul,
    ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul, Fintype.expect_ite_eq]
  simp [NNRat.smul_def (K := ℂ), Fintype.card_ne_zero]

/-- The normalized additive convolution `E_y f y * g (x-y)`. -/
def convolution (f g : G → ℂ) (x : G) : ℂ :=
  𝔼 y : G, f y * g (x - y)

/-- The normalized difference convolution `E_y f (x+y) * conj (g y)`.

For real-valued functions this is the usual additive-combinatorial difference
convolution.  The conjugation makes autocorrelation positive on the Fourier side.
-/
def differenceConvolution (f g : G → ℂ) (x : G) : ℂ :=
  𝔼 y : G, f (x + y) * conj (g y)

lemma coeff_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    coeff (convolution f g) χ = coeff f χ * coeff g χ := by
  classical
  simp_rw [coeff, wInner_cWeight_eq_expect, inner_apply, convolution,
    mul_expect, expect_mul, ← expect_product', univ_product_univ]
  refine Fintype.expect_equiv ((Equiv.prodComm _ _).trans <|
    ((Equiv.refl _).prodShear Equiv.subRight).trans <| Equiv.prodComm _ _) _ _ fun (a, b) ↦ ?_
  simp [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul]

lemma coeff_conjneg (f : G → ℂ) (χ : AddChar G ℂ) :
    coeff (fun x ↦ conj (f (-x))) χ = conj (coeff f χ) := by
  classical
  simp only [coeff, wInner_cWeight_eq_expect, inner_apply, map_expect, map_mul,
    RCLike.conj_conj]
  refine Fintype.expect_equiv (Equiv.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

lemma differenceConvolution_eq_convolution (f g : G → ℂ) :
    differenceConvolution f g = convolution f (fun x ↦ conj (g (-x))) := by
  funext x
  simp only [differenceConvolution, convolution]
  refine Fintype.expect_equiv (Equiv.addLeft x) _ _ fun y ↦ ?_
  simp

lemma coeff_differenceConvolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    coeff (differenceConvolution f g) χ = coeff f χ * conj (coeff g χ) := by
  rw [differenceConvolution_eq_convolution, coeff_convolution, coeff_conjneg]

/-- The Fourier coefficient of an autocorrelation is a squared absolute value. -/
lemma coeff_autocorrelation (f : G → ℂ) (χ : AddChar G ℂ) :
    coeff (differenceConvolution f f) χ = (Complex.normSq (coeff f χ) : ℂ) := by
  rw [coeff_differenceConvolution]
  exact Complex.mul_conj _

end FiniteFourier

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Chang.lean` -/

section
/-!
# Chang's large-spectrum lemma for a finite abelian group

This file supplies the part of Chang's lemma needed in the quantitative Roth
argument.  The Fourier coefficient of the indicator of `A` at `psi` is kept
unnormalized:

`sum x in A, psi x`.

Consequently `largeSpectrum A eta` consists of the characters for which the
norm of this sum is at least `eta * #A`.  The final theorem covers this
spectrum by the `{0, 1, -1}`-span of at most

`ceil (2 * log (|G| / |A|) / eta^2)`

characters.

The analytic input is proved here.  It is the exponential form of Rudin's
inequality for a polynomial whose character support is dissociated.  Jensen's
inequality on `A`, followed by Rudin's inequality on `G`, gives the stated
dimension bound directly.
-/

open _root_.Finset _root_.Function _root_.Real
open _root_.Complex (re)
open scoped BigOperators ComplexConjugate

namespace Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-! ## Exponential Rudin inequality -/

/-! ## Large spectrum -/

/-- The unnormalized Fourier sum of `1_A` at a character. -/
noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

/-- The characters on which the Fourier transform of `1_A` has magnitude at
least `eta * |A|`. -/
noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

/-! ## Chang's covering theorem -/

end Chang

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RegularSpectrumPhase.lean` -/

section
/-!
# Large-spectrum characters on a regular Bohr set

A character in the large spectrum of a regular Bohr carrier is almost
constant on a sufficiently small dilate.  The proof keeps the constants
explicit: the exact Fourier translation identity converts the phase error
into the counting-measure `L¹` translation error for the normalized
indicator, to which rank regularity applies.
-/

open _root_.AddChar _root_.Finset
open scoped BigOperators _root_.NNReal

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private lemma normalizedSpectrum_eq (A : Finset G) (psi : AddChar G ℂ) :
    (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
      ((A.card : ℂ)⁻¹) * Chang.spectrumSum A psi := by
  classical
  rw [Chang.spectrumSum, Finset.mul_sum]
  calc
    (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
        ∑ x : G, if x ∈ A then ((A.card : ℂ)⁻¹) * psi x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [normalizedIndicator, hx]
    _ = ∑ x ∈ A, ((A.card : ℂ)⁻¹) * psi x := by
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.univ.filter fun x : G ↦ x ∈ A) = A := by
        ext x
        simp
      rw [hfilter]

private lemma normalizedSpectrum_translate (A : Finset G)
    (psi : AddChar G ℂ) (t : G) :
    (1 - psi t) * (∑ x : G, (normalizedIndicator A x : ℂ) * psi x) =
      ∑ x : G,
        ((normalizedIndicator A x - normalizedIndicator A (x - t) : ℝ) : ℂ) *
          psi x := by
  classical
  have htranslate :
      (∑ x : G, (normalizedIndicator A (x - t) : ℂ) * psi x) =
        psi t * ∑ x : G, (normalizedIndicator A x : ℂ) * psi x := by
    rw [← (Equiv.addRight t).sum_comp]
    · change
        (∑ x : G, (normalizedIndicator A ((x + t) - t) : ℂ) * psi (x + t)) =
          psi t * ∑ x : G, (normalizedIndicator A x : ℂ) * psi x
      simp_rw [add_sub_cancel_right, map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    · simp
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, htranslate]
  ring

/-- A character in the `eta`-large spectrum of a rank-regular Bohr carrier
has phase variation at most `200 * max(rank,1) * sigma / eta` on the
`sigma`-dilate. -/
theorem norm_one_sub_le_of_mem_largeSpectrum
    {C : BohrData G} (hreg : C.IsRankRegular) {eta : ℝ} (heta : 0 < eta)
    {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar G ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier eta)
    {t : G} (ht : t ∈ (C.dilate sigma).carrier) :
    ‖1 - psi t‖ ≤
      200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) / eta := by
  classical
  let F : ℂ := ∑ x : G, (normalizedIndicator C.carrier x : ℂ) * psi x
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hFnorm : ‖F‖ = ‖Chang.spectrumSum C.carrier psi‖ / C.carrier.card := by
    dsimp [F]
    rw [normalizedSpectrum_eq, norm_mul]
    simp [div_eq_inv_mul]
  have hlarge : eta ≤ ‖F‖ := by
    rw [hFnorm, le_div_iff₀ hcard]
    exact Chang.mem_largeSpectrum.mp hpsi
  have hphase :
      ‖1 - psi t‖ * ‖F‖ ≤
        ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := by
    rw [← norm_mul, normalizedSpectrum_translate C.carrier psi t]
    calc
      ‖∑ x : G,
          ((normalizedIndicator C.carrier x -
              normalizedIndicator C.carrier (x - t) : ℝ) : ℂ) * psi x‖ ≤
          ∑ x : G,
            ‖((normalizedIndicator C.carrier x -
                normalizedIndicator C.carrier (x - t) : ℝ) : ℂ) * psi x‖ :=
        norm_sum_le _ _
      _ = ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        simp
  have htranslation :=
    BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
      hreg hsigma ht
  have hmul :
      ‖1 - psi t‖ * eta ≤
        200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
    calc
      ‖1 - psi t‖ * eta ≤ ‖1 - psi t‖ * ‖F‖ :=
        mul_le_mul_of_nonneg_left hlarge (norm_nonneg _)
      _ ≤ ∑ x : G,
          |normalizedIndicator C.carrier (x - t) -
            normalizedIndicator C.carrier x| := hphase
      _ ≤ 200 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := htranslation
  exact (le_div_iff₀ heta).2 hmul

/-- Threshold-`1/2` specialization of
`norm_one_sub_le_of_mem_largeSpectrum`. -/
theorem norm_one_sub_le_of_mem_largeSpectrum_half
    {C : BohrData G} (hreg : C.IsRankRegular) {sigma : ℝ≥0}
    (hsigma : sigma ≤ 1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    {psi : AddChar G ℂ} (hpsi : psi ∈ Chang.largeSpectrum C.carrier (1 / 2))
    {t : G} (ht : t ∈ (C.dilate sigma).carrier) :
    ‖1 - psi t‖ ≤ 400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  have h := norm_one_sub_le_of_mem_largeSpectrum hreg (eta := (1 / 2 : ℝ))
    (by norm_num) hsigma hpsi ht
  convert h using 1
  ring

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RelativeChangDefinitions.lean` -/

section
/-!
# Basic definitions for the relative Chang--Sanders lemma

This small module contains the definitions shared by the analytic dimension
bound, the relative-dissociation selection, and the indicator bridge.  It is
kept separate so that the final assembled theorem can import all three
components without an import cycle.
-/

noncomputable section

open _root_.Finset _root_.Function _root_.Real
open scoped BigOperators ComplexConjugate _root_.NNReal

namespace RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Sanders' measure-relative replacement for ordinary dissociativity. -/
def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

/-- The spectrum of `f` relative to a probability measure `mu`. -/
def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end RelativeChangSanders

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RelativeSpectrumBridge.lean` -/

section
/-!
# Normalization bridge for the relative large spectrum

This file identifies the weighted spectrum of an indicator inside a finite
Bohr carrier with the unnormalised indicator spectrum used by `Chang.lean`.
The factors of the carrier cardinality are recorded explicitly.
-/

open _root_.Finset
open scoped BigOperators

namespace RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-! ## A general constant-on-the-ambient-set bridge -/

/-- If `w` is constant with value `c` on an ambient set containing `X`, then
the weighted mass of `1_X` is `c * |X|`. -/
theorem sum_finsetIndicator_mul_eq_const_mul_card
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) :
    ∑ x : G, finsetIndicator X x * w x = c * X.card := by
  classical
  calc
    ∑ x : G, finsetIndicator X x * w x = ∑ x ∈ X, c := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = c * X.card := by simp [mul_comm]

/-- Fourier-sum version of `sum_finsetIndicator_mul_eq_const_mul_card`. -/
theorem sum_finsetIndicator_mul_character_eq_const_mul
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (psi : AddChar G ℂ) :
    ∑ x : G, ((finsetIndicator X x * w x : ℝ) : ℂ) * psi x =
      (c : ℂ) * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G, ((finsetIndicator X x * w x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (c : ℂ) * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [finsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [finsetIndicator, hxX]
    _ = (c : ℂ) * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

/-- A positive weight which is constant on the ambient set does not change
the large spectrum of an indicator. -/
theorem mem_relativeLargeSpectrum_of_eq_const_iff
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (hc : 0 < c)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum w (finsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_finsetIndicator_mul_eq_const_mul_card hXB hw]
  rw [sum_finsetIndicator_mul_character_eq_const_mul hXB hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  constructor
  · intro h
    have hh : c * (eta * (X.card : ℝ)) ≤
        c * ‖Chang.spectrumSum X psi‖ := by
      calc
        c * (eta * (X.card : ℝ)) = eta * (c * (X.card : ℝ)) := by ring
        _ ≤ c * ‖Chang.spectrumSum X psi‖ := h
    nlinarith
  · intro h
    calc
      eta * (c * (X.card : ℝ)) = c * (eta * (X.card : ℝ)) := by ring
      _ ≤ c * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h hc.le

end RelativeSpectrumBridge

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BohrSmoothingMeasure.lean` -/

section
/-!
# Convolution-power smoothing measures on finite Bohr sets

This file supplies the counting-measure probability kernels used in the
relative Chang--Sanders argument.  The normalization is the one from
`FiniteConvolution.lean`: convolution is an ordinary finite sum, while each
nonempty normalized indicator has total mass one.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Convolution powers -/

/-- The counting-convolution power of a real function.  The zeroth power is
the unit point mass at the origin. -/
def convolutionPower (f : G → ℝ) : ℕ → G → ℝ
  | 0 => normalizedIndicator {0}
  | n + 1 => normalizedConvolution (convolutionPower f n) f

@[simp] theorem convolutionPower_zero (f : G → ℝ) :
    convolutionPower f 0 = normalizedIndicator {0} := rfl

@[simp] theorem convolutionPower_succ (f : G → ℝ) (n : ℕ) :
    convolutionPower f (n + 1) =
      normalizedConvolution (convolutionPower f n) f := rfl

/-- A convolution power of a nonnegative function is nonnegative. -/
theorem convolutionPower_nonneg {f : G → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∀ n x, 0 ≤ convolutionPower f n x := by
  intro n
  induction n with
  | zero =>
      exact normalizedIndicator_nonneg {0}
  | succ n ihn =>
      exact normalizedConvolution_nonneg ihn hf

/-- A convolution power of a probability density again has mass one. -/
theorem sum_convolutionPower {f : G → ℝ} (hf : ∑ x : G, f x = 1) :
    ∀ n, ∑ x : G, convolutionPower f n x = 1 := by
  intro n
  induction n with
  | zero =>
      exact sum_normalizedIndicator (singleton_nonempty 0)
  | succ n ihn =>
      rw [convolutionPower_succ, sum_normalizedConvolution, ihn, hf, one_mul]

/-- The `n`-fold convolution of the normalized measure of `B_σ` is
supported on `B_(nσ)`. -/
theorem convolutionPower_normalizedIndicator_support
    (B : BohrData G) (σ : ℝ≥0) :
    ∀ n x, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n x ≠ 0 →
      x ∈ (B.dilate ((n : ℝ≥0) * σ)).carrier := by
  intro n
  induction n with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by
        simpa using
          (normalizedIndicator_ne_zero_iff (singleton_nonempty 0) x).mp hx
      subst x
      simpa using (B.dilate 0).zero_mem_carrier
  | succ n ihn =>
      intro x hx
      rw [convolutionPower_succ, normalizedConvolution] at hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have hypow : convolutionPower (normalizedIndicator (B.dilate σ).carrier) n y ≠ 0 :=
        (mul_ne_zero_iff.mp hy).1
      have hysmall : normalizedIndicator (B.dilate σ).carrier (x - y) ≠ 0 :=
        (mul_ne_zero_iff.mp hy).2
      have hyB := ihn y hypow
      have hxyB : x - y ∈ (B.dilate σ).carrier :=
        (normalizedIndicator_ne_zero_iff
          (B.dilate σ).carrier_nonempty (x - y)).mp hysmall
      have hadd := BohrData.add_mem_dilate hyB hxyB
      have hxsum : y + (x - y) = x := by simp [add_comm]
      rw [hxsum] at hadd
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using hadd

/-! ## Counting-mass Fourier coefficients -/

/-- The unnormalized Fourier coefficient of a real counting-mass density.
There is deliberately no ambient factor `|G|⁻¹` here. -/
def massCoeff (w : G → ℝ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, (w x : ℂ) * ψ x

/-- The mass coefficient of a normalized indicator is its unnormalized
indicator Fourier sum divided by the cardinality. -/
theorem massCoeff_normalizedIndicator (A : Finset G) (ψ : AddChar G ℂ) :
    massCoeff (normalizedIndicator A) ψ =
      ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
  calc
    massCoeff (normalizedIndicator A) ψ =
        ∑ x ∈ A, ((A.card : ℝ)⁻¹ : ℂ) * ψ x := by
      rw [massCoeff, ← Finset.sum_subset (s₁ := A) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [normalizedIndicator, hx]
      · simp
      · intro x hxU hxA
        simp [normalizedIndicator, hxA]
    _ = ((A.card : ℝ)⁻¹ : ℂ) * Chang.spectrumSum A ψ := by
      rw [Chang.spectrumSum, Finset.mul_sum]

/-- Outside Chang's half-large spectrum, the normalized indicator has mass
Fourier coefficient strictly smaller than one half. -/
theorem norm_massCoeff_normalizedIndicator_lt_half_of_not_mem_largeSpectrum
    (C : BohrData G) (ψ : AddChar G ℂ)
    (hψ : ψ ∉ Chang.largeSpectrum C.carrier (1 / 2)) :
    ‖massCoeff (normalizedIndicator C.carrier) ψ‖ < 1 / 2 := by
  have hcard : (0 : ℝ) < C.carrier.card := by
    exact_mod_cast C.carrier_nonempty.card_pos
  have hspectrum :
      ‖Chang.spectrumSum C.carrier ψ‖ < (1 / 2 : ℝ) * C.carrier.card := by
    apply lt_of_not_ge
    intro h
    exact hψ (Chang.mem_largeSpectrum.mpr h)
  calc
    ‖massCoeff (normalizedIndicator C.carrier) ψ‖ =
        (C.carrier.card : ℝ)⁻¹ * ‖Chang.spectrumSum C.carrier ψ‖ := by
      rw [massCoeff_normalizedIndicator, norm_mul]
      simp [norm_inv, Complex.norm_natCast]
    _ < (C.carrier.card : ℝ)⁻¹ *
        ((1 / 2 : ℝ) * C.carrier.card) :=
      mul_lt_mul_of_pos_left hspectrum (inv_pos.mpr hcard)
    _ = 1 / 2 := by field_simp

/-- Counting convolution turns into multiplication of mass Fourier
coefficients. -/
theorem massCoeff_normalizedConvolution (f g : G → ℝ) (ψ : AddChar G ℂ) :
    massCoeff (normalizedConvolution f g) ψ = massCoeff f ψ * massCoeff g ψ := by
  unfold massCoeff normalizedConvolution
  push_cast
  calc
    ∑ x : G, (∑ y : G, (f y : ℂ) * (g (x - y) : ℂ)) * ψ x =
        ∑ x : G, ∑ y : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_mul]
    _ = ∑ y : G, ∑ x : G, (f y : ℂ) * (g (x - y) : ℂ) * ψ x :=
      Finset.sum_comm
    _ =
        ∑ y : G, ((f y : ℂ) * ψ y) *
          ∑ z : G, (g z : ℂ) * ψ z := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z ↦ ?_
      have hψ : ψ z = ψ y * ψ (z - y) := by
        calc
          ψ z = ψ (y + (z - y)) := congrArg ψ (by simp [add_comm])
          _ = ψ y * ψ (z - y) := AddChar.map_add_eq_mul ψ y (z - y)
      simp only [Equiv.subRight_apply]
      rw [hψ]
      ring
    _ = (∑ y : G, (f y : ℂ) * ψ y) *
        ∑ z : G, (g z : ℂ) * ψ z := by
      simpa using
        (Finset.sum_mul (univ : Finset G) (fun y ↦ (f y : ℂ) * ψ y)
          (∑ z : G, (g z : ℂ) * ψ z)).symm

/-- Fourier coefficients of convolution powers are ordinary powers. -/
theorem massCoeff_convolutionPower (f : G → ℝ) (ψ : AddChar G ℂ) :
    ∀ n, massCoeff (convolutionPower f n) ψ = massCoeff f ψ ^ n := by
  intro n
  induction n with
  | zero =>
      unfold massCoeff
      rw [Fintype.sum_eq_single 0]
      · simp [normalizedIndicator]
      · intro y hy
        simp [normalizedIndicator, hy]
  | succ n ihn =>
      rw [convolutionPower_succ, massCoeff_normalizedConvolution, ihn, pow_succ]

/-- A nonnegative mass has Fourier magnitude at most its total mass. -/
theorem norm_massCoeff_le_sum {w : G → ℝ} (hw : ∀ x, 0 ≤ w x)
    (ψ : AddChar G ℂ) :
    ‖massCoeff w ψ‖ ≤ ∑ x : G, w x := by
  unfold massCoeff
  calc
    ‖∑ x : G, (w x : ℂ) * ψ x‖ ≤
        ∑ x : G, ‖(w x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x : G, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [norm_mul, hw x]

/-! ## The Bohr smoothing measure -/

/-- The outer Bohr probability measure smoothed by `n` copies of the inner
measure at scale `σ`. -/
def bohrSmoothingMeasure (B : BohrData G) (σ : ℝ≥0) (n : ℕ) : G → ℝ :=
  normalizedConvolution
    (normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier)
    (convolutionPower (normalizedIndicator (B.dilate σ).carrier) n)

/-- The Bohr smoothing measure is nonnegative. -/
theorem bohrSmoothingMeasure_nonneg (B : BohrData G) (σ : ℝ≥0) (n : ℕ) (x : G) :
    0 ≤ bohrSmoothingMeasure B σ n x := by
  exact normalizedConvolution_nonneg
    (normalizedIndicator_nonneg _)
    (convolutionPower_nonneg (normalizedIndicator_nonneg _) n) x

/-- The Bohr smoothing measure has total mass one. -/
theorem sum_bohrSmoothingMeasure (B : BohrData G) (σ : ℝ≥0) (n : ℕ) :
    ∑ x : G, bohrSmoothingMeasure B σ n x = 1 := by
  rw [bohrSmoothingMeasure, sum_normalizedConvolution,
    sum_normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty,
    sum_convolutionPower
      (sum_normalizedIndicator (B.dilate σ).carrier_nonempty), one_mul]

/-- On the central carrier, the smoothing measure is exactly the constant
value of its outer normalized Bohr measure. -/
theorem bohrSmoothingMeasure_apply_of_mem
    (B : BohrData G) (σ : ℝ≥0) (n : ℕ) {x : G} (hx : x ∈ B.carrier) :
    bohrSmoothingMeasure B σ n x =
      (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
  rw [bohrSmoothingMeasure, normalizedConvolution_comm]
  simp only [normalizedConvolution]
  calc
    ∑ t : G, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t *
          normalizedIndicator (B.dilate (1 + (n : ℝ≥0) * σ)).carrier (x - t) =
        ∑ t : G, convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t *
          (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hνt :
          convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t = 0
      · simp [hνt]
      · have htB : t ∈ (B.dilate ((n : ℝ≥0) * σ)).carrier :=
          convolutionPower_normalizedIndicator_support B σ n t hνt
        have hxt : x - t ∈
            (B.dilate (1 + (n : ℝ≥0) * σ)).carrier := by
          exact BohrData.sub_mem_dilate
            (B := B) (s := 1) (t := (n : ℝ≥0) * σ)
            (by simpa using hx) htB
        rw [normalizedIndicator_apply_mem hxt]
    _ = (∑ t : G,
          convolutionPower (normalizedIndicator (B.dilate σ).carrier) n t) *
        (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (((B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card : ℝ)⁻¹) := by
      rw [sum_convolutionPower
        (sum_normalizedIndicator (B.dilate σ).carrier_nonempty)]
      simp

/-- Rank regularity bounds the carrier at the total smoothing radius by
twice the central carrier. -/
theorem card_dilate_one_add_le_two_mul
    {B : BohrData G} (hreg : B.IsRankRegular) {σ : ℝ≥0} (n : ℕ)
    (hsmall : (n : ℝ≥0) * σ ≤
      1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0)) :
    (B.dilate (1 + (n : ℝ≥0) * σ)).carrier.card ≤
      2 * B.carrier.card := by
  let κ : ℝ≥0 := (n : ℝ≥0) * σ
  let d : ℕ := max B.rank 1
  have hcards := hreg κ (by simpa [κ, d] using hsmall)
  have hfactor : (1 + 100 * (d : ℝ) * (κ : ℝ)) ≤ 2 := by
    have hsmallR : (κ : ℝ) ≤ 1 / (100 * (d : ℝ)) := by
      exact_mod_cast (show κ ≤ 1 / (100 * (d : ℝ≥0)) by
        simpa [κ, d] using hsmall)
    have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by simp [d])
    calc
      1 + 100 * (d : ℝ) * (κ : ℝ) ≤
          1 + 100 * (d : ℝ) * (1 / (100 * (d : ℝ))) := by gcongr
      _ = 2 := by field_simp; ring
  have hcardR :
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.dilate (1 + κ)).carrier.card : ℝ) ≤
          (1 + 100 * (d : ℝ) * (κ : ℝ)) * (B.carrier.card : ℝ) := by
        simpa [κ, d] using hcards.2
      _ ≤ 2 * (B.carrier.card : ℝ) := by gcongr
  exact_mod_cast hcardR

/-- The outer normalized Bohr factor has Fourier magnitude at most one, so
the smoothing measure inherits the `n`th power decay of its inner factor. -/
theorem norm_massCoeff_bohrSmoothingMeasure_le
    (B : BohrData G) (σ : ℝ≥0) (n : ℕ) (ψ : AddChar G ℂ) :
    ‖massCoeff (bohrSmoothingMeasure B σ n) ψ‖ ≤
      ‖massCoeff (normalizedIndicator (B.dilate σ).carrier) ψ‖ ^ n := by
  rw [bohrSmoothingMeasure, massCoeff_normalizedConvolution,
    massCoeff_convolutionPower, norm_mul, norm_pow]
  have houter :
      ‖massCoeff (normalizedIndicator
        (B.dilate (1 + (n : ℝ≥0) * σ)).carrier) ψ‖ ≤ 1 := by
    simpa [sum_normalizedIndicator
      (B.dilate (1 + (n : ℝ≥0) * σ)).carrier_nonempty] using
      norm_massCoeff_le_sum
        (w := normalizedIndicator
          (B.dilate (1 + (n : ℝ≥0) * σ)).carrier)
        (normalizedIndicator_nonneg _) ψ
  exact mul_le_of_le_one_left (by positivity) houter

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RelativeDissociation.lean` -/

section
/-!
# Dissociation relative to a spectrum

This file records the elementary ``dissociated modulo a set'' selection
which is used in Sanders' relative form of Chang's lemma, together with the
corresponding approximate Riesz-product randomisation estimate.
-/

noncomputable section

open _root_.Finset _root_.Real
open scoped BigOperators ComplexConjugate

namespace RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- A finite family is dissociated modulo `S` if no nonempty signed sum of
distinct members, with signs in `{-1, 1}`, belongs to `S`.

The two disjoint finsets are respectively the positive and negative parts of
the signed sum. -/
def AddDissociatedMod (S Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ t u : Finset (AddChar G ℂ), t ⊆ Delta → u ⊆ Delta →
    Disjoint t u → (t ∪ u).Nonempty →
      (∑ psi ∈ t, psi) - ∑ psi ∈ u, psi ∉ S

theorem addDissociatedMod_empty (S : Finset (AddChar G ℂ)) :
    AddDissociatedMod S ∅ := by
  intro t u ht hu htu hne
  simp only [Finset.subset_empty] at ht hu
  subst t
  subst u
  simpa using hne

theorem AddDissociatedMod.mono {S : Finset (AddChar G ℂ)}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : AddDissociatedMod S Delta) (hsub : Gamma ⊆ Delta) :
    AddDissociatedMod S Gamma := by
  intro t u ht hu
  exact h t u (ht.trans hsub) (hu.trans hsub)

/-- Maximal dissociation modulo a negation-invariant set gives a signed-span
cover. -/
theorem exists_maximal_addDissociatedMod
    (S T : Finset (AddChar G ℂ))
    (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  classical
  let candidates := T.powerset.filter (AddDissociatedMod S)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, addDissociatedMod_empty]
  obtain ⟨Delta, hDelta_mem, hDelta_max⟩ := candidates.exists_maximal hcandidates
  have hDelta := Finset.mem_filter.mp hDelta_mem
  refine ⟨Delta, Finset.mem_powerset.mp hDelta.1, hDelta.2, ?_⟩
  intro psi hpsiT
  by_cases hpsiDelta : psi ∈ Delta
  · exact ⟨psi, Finset.subset_addSpan hpsiDelta, 0, hzero, by simp⟩
  · have hinsert_subset : insert psi Delta ⊆ T :=
      Finset.insert_subset hpsiT (Finset.mem_powerset.mp hDelta.1)
    have hnot : ¬ AddDissociatedMod S (insert psi Delta) := by
      intro hins
      have hinsert_mem : insert psi Delta ∈ candidates := by
        simp [candidates, hinsert_subset, hins]
      have hsub := hDelta_max hinsert_mem (Finset.subset_insert psi Delta)
      exact hpsiDelta (hsub (Finset.mem_insert_self psi Delta))
    rw [AddDissociatedMod] at hnot
    push_neg at hnot
    obtain ⟨t, u, ht, hu, htu, hne, hsumS⟩ := hnot
    have hpsi_tu : psi ∈ t ∪ u := by
      by_contra hpsi
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_left u ha))
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_right t ha))
      exact hDelta.2 t u htDelta huDelta htu hne hsumS
    rw [Finset.mem_union] at hpsi_tu
    rcases hpsi_tu with hpsi_t | hpsi_u
    · have hpsi_not_u : psi ∉ u := fun h ↦ Finset.disjoint_left.mp htu hpsi_t h
      have htErase : t.erase psi ⊆ Delta := by
        intro a ha
        have ha' := ht (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_u (h ▸ ha))
      let z := (∑ a ∈ u, a) - ∑ a ∈ t.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan huDelta htErase
      refine ⟨z, hz, (∑ a ∈ t, a) - ∑ a ∈ u, a, hsumS, ?_⟩
      dsimp [z]
      rw [← Finset.sum_erase_add _ _ hpsi_t]
      abel
    · have hpsi_not_t : psi ∉ t := fun h ↦ Finset.disjoint_left.mp htu h hpsi_u
      have huErase : u.erase psi ⊆ Delta := by
        intro a ha
        have ha' := hu (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_t (h ▸ ha))
      let z := (∑ a ∈ t, a) - ∑ a ∈ u.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan htDelta huErase
      let s := -((∑ a ∈ t, a) - ∑ a ∈ u, a)
      have hs : s ∈ S := hS _ hsumS
      refine ⟨z, hz, s, hs, ?_⟩
      dsimp [z, s]
      rw [← Finset.sum_erase_add _ _ hpsi_u]
      abel

private def signedFrequency (t u : Finset (AddChar G ℂ)) : AddChar G ℂ :=
  (∑ psi ∈ u, psi) - ∑ psi ∈ t \ u, psi

private def signedCoefficient (v : AddChar G ℂ → ℂ)
    (t u : Finset (AddChar G ℂ)) : ℂ :=
  ((∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)) /
    (2 : ℂ) ^ t.card

private lemma rieszProduct_eq_signedExpansion
    (Delta : Finset (AddChar G ℂ)) (v : AddChar G ℂ → ℂ) (x : G) :
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
  calc
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
        ∏ psi ∈ Delta,
          (((v psi * psi x) + conj (v psi * psi x)) / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro psi hpsi
      rw [add_comm, ← Complex.re_eq_add_conj]
      push_cast
      rfl
    _ = ∑ t ∈ Delta.powerset,
        ∏ psi ∈ t, ((v psi * psi x) + conj (v psi * psi x)) / 2 := by
      rw [Finset.prod_add]
      simp
    _ = ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      rw [Finset.prod_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [signedCoefficient, signedFrequency]
      simp only [AddChar.sum_apply, AddChar.sub_apply,
        AddChar.map_neg_eq_conj]
      simp only [Finset.prod_const]
      simp_rw [map_mul, Finset.prod_mul_distrib]
      rw [map_prod]
      ring

private lemma weightedRiesz_eq_signedExpansion
    (w : G → ℝ) (Delta : Finset (AddChar G ℂ))
    (v : AddChar G ℂ → ℂ) :
    ((∑ x : G, w x *
        ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u *
          Erdos140.massCoeff w (signedFrequency t u) := by
  simp_rw [Complex.ofReal_prod]
  simp_rw [rieszProduct_eq_signedExpansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos140.massCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private lemma signedFrequency_not_mem
    {S Delta t u : Finset (AddChar G ℂ)}
    (hDelta : AddDissociatedMod S Delta)
    (ht : t ⊆ Delta) (ht0 : t.Nonempty) (hu : u ⊆ t) :
    signedFrequency t u ∉ S := by
  apply hDelta u (t \ u)
  · exact hu.trans ht
  · exact Finset.sdiff_subset.trans ht
  · rw [Finset.disjoint_left]
    intro psi hpsiu hpsitu
    exact (Finset.mem_sdiff.mp hpsitu).2 hpsiu
  · simpa [Finset.union_sdiff_of_subset hu] using ht0

private lemma norm_signedCoefficient_le
    {v : AddChar G ℂ → ℂ} {t u : Finset (AddChar G ℂ)}
    (hu : u ⊆ t) (hv : ∀ psi ∈ t, ‖v psi‖ ≤ 1) :
    ‖signedCoefficient v t u‖ ≤ ((2 : ℝ) ^ t.card)⁻¹ := by
  have hvu : ‖∏ psi ∈ u, v psi‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ hv psi (hu hpsi))
  have hvtu : ‖∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ by
        rw [RCLike.norm_conj]
        exact hv psi (Finset.sdiff_subset hpsi))
  have hnum :
      ‖(∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hvu hvtu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [signedCoefficient, norm_div]
  calc
    _ ≤ 1 / ‖(2 : ℂ) ^ t.card‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = ((2 : ℝ) ^ t.card)⁻¹ := by
      rw [norm_pow]
      norm_num

/-- Approximate weighted randomisation for a family dissociated modulo `S`.
The empty Fourier term contributes the mass of `w`; every other signed
frequency lies outside `S`. -/
theorem AddDissociatedMod.weighted_riesz_randomisation_le
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ}
    (hDelta : AddDissociatedMod S Delta)
    (_hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (v : AddChar G ℂ → ℂ) (hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1) :
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
      1 + q * (2 : ℝ) ^ Delta.card := by
  classical
  let F : Finset (AddChar G ℂ) → ℂ := fun t ↦
    ∑ u ∈ t.powerset, signedCoefficient v t u *
      Erdos140.massCoeff w (signedFrequency t u)
  let E : ℂ := ∑ t ∈ Delta.powerset.erase ∅, F t
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ Delta.powerset := by simp
  have hw1c : ∑ x : G, (w x : ℂ) = 1 := by exact_mod_cast hw1
  have hFempty : F ∅ = 1 := by
    simp [F, signedCoefficient, signedFrequency, Erdos140.massCoeff, hw1c]
  have hexp :
      ((∑ x : G, w x *
          ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) = 1 + E := by
    rw [weightedRiesz_eq_signedExpansion]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [hFempty, E, F]
    ring
  have hinner (t : Finset (AddChar G ℂ))
      (ht : t ∈ Delta.powerset.erase ∅) : ‖F t‖ ≤ q := by
    have htDelta : t ⊆ Delta := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have ht0 : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    calc
      ‖F t‖ ≤ ∑ u ∈ t.powerset,
          ‖signedCoefficient v t u *
            Erdos140.massCoeff w (signedFrequency t u)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _u ∈ t.powerset, ((2 : ℝ) ^ t.card)⁻¹ * q := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_signedCoefficient_le (Finset.mem_powerset.mp hu)
            (fun psi hpsi ↦ hv psi (htDelta hpsi))
        · exact hq _ (signedFrequency_not_mem hDelta htDelta ht0
            (Finset.mem_powerset.mp hu))
        · exact norm_nonneg _
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
      _ = q := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul]
  have hEnorm : ‖E‖ ≤ q * (2 : ℝ) ^ Delta.card := by
    calc
      ‖E‖ ≤ ∑ t ∈ Delta.powerset.erase ∅, ‖F t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Delta.powerset.erase ∅, q := by
        exact Finset.sum_le_sum fun t ht ↦ hinner t ht
      _ ≤ ∑ _t ∈ Delta.powerset, q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ hq0)
      _ = q * (2 : ℝ) ^ Delta.card := by
        simp [Finset.card_powerset]
        ring
  let R : ℝ :=
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re)
  have hexpR : (R : ℂ) = 1 + E := by
    calc
      (R : ℂ) = ∑ x : G, (w x : ℂ) *
          (↑(∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) := by
        dsimp [R]
        push_cast
        rfl
      _ = 1 + E := hexp
  have hre : R = 1 + E.re := by
    have := congrArg Complex.re hexpR
    simpa using this
  change R ≤ 1 + q * (2 : ℝ) ^ Delta.card
  calc
    R = 1 + E.re := hre
    _ ≤ 1 + ‖E‖ := add_le_add (le_refl 1) (Complex.re_le_norm E)
    _ ≤ 1 + q * (2 : ℝ) ^ Delta.card := add_le_add (le_refl 1) hEnorm

/-- A small spectral tail turns dissociation modulo `S` into Sanders'
weighted dissociativity. -/
theorem AddDissociatedMod.isWeightedDissociated
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hqk : q * (2 : ℝ) ^ k ≤ 1) :
    IsWeightedDissociated w 1 Delta := by
  intro v hv
  have hpowNat : 2 ^ Delta.card ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hpow : (2 : ℝ) ^ Delta.card ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hpowNat
  have htail : q * (2 : ℝ) ^ Delta.card ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hq0).trans hqk
  calc
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
        1 + q * (2 : ℝ) ^ Delta.card :=
      hDelta.weighted_riesz_randomisation_le hw0 hw1 hq0 hq v hv
    _ ≤ 2 := by linarith
    _ ≤ exp 1 := Real.exp_one_gt_two.le

/-- Convenient `4^{-k}` specialization of
`AddDissociatedMod.isWeightedDissociated`. -/
theorem AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos140.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hq_quarter : q ≤ (1 / 4 : ℝ) ^ k) :
    IsWeightedDissociated w 1 Delta := by
  apply hDelta.isWeightedDissociated hw0 hw1 hq0 hq hcard
  calc
    q * (2 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hq_quarter (pow_nonneg (by norm_num) _)
    _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; congr 1 <;> norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-! ## The ordinary large spectrum is symmetric -/

theorem zero_mem_chang_largeSpectrum_half (A : Finset G) :
    (0 : AddChar G ℂ) ∈ Erdos140.Chang.largeSpectrum A (1 / 2 : ℝ) := by
  rw [Erdos140.Chang.mem_largeSpectrum]
  simp [Erdos140.Chang.spectrumSum]
  have hcard : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le A.card
  nlinarith

theorem neg_mem_chang_largeSpectrum {A : Finset G} {eta : ℝ}
    {psi : AddChar G ℂ}
    (hpsi : psi ∈ Erdos140.Chang.largeSpectrum A eta) :
    -psi ∈ Erdos140.Chang.largeSpectrum A eta := by
  rw [Erdos140.Chang.mem_largeSpectrum] at hpsi ⊢
  have hsum : Erdos140.Chang.spectrumSum A (-psi) =
      conj (Erdos140.Chang.spectrumSum A psi) := by
    unfold Erdos140.Chang.spectrumSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [AddChar.neg_apply, AddChar.map_neg_eq_conj]
  rw [hsum, RCLike.norm_conj]
  exact hpsi

end RelativeChangSanders

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RelativeChangSanders.lean` -/

section
/-!
# The relative Chang--Sanders lemma

This file develops the local spectral input used in the Bohr-set form of
Schoen--Sisask almost-periodicity.  The analytic notion of dissociativity is
relative to a probability measure.  This is the formulation introduced by
Sanders: unlike ordinary dissociativity it gives bounds in terms of the
relative density inside a Bohr set, with no ambient-density loss.
-/

noncomputable section

open _root_.Finset _root_.Function _root_.Real
open scoped BigOperators ComplexConjugate _root_.NNReal

namespace RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- Jensen's inequality for an arbitrary nonnegative finite probability
weight.  Keeping this lemma in finite-sum form avoids introducing a second
measure-theoretic normalization layer. -/
theorem exp_weightedAverage_le_weightedAverage_exp
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw_sum : ∑ x : G, w x = 1)
    (f : G → ℝ) :
    exp (∑ x : G, w x * f x) ≤ ∑ x : G, w x * exp (f x) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset G))
    (p := f) (fun x _ ↦ hw x) (by simpa using hw_sum)
    (fun x _ ↦ Set.mem_univ (f x))
  simpa using h

/-- Weighted exponential Rudin inequality.  Ordinary Rudin is the special
case in which `mu` is uniform and `K = 0`; the proof only uses the defining
Riesz-product estimate, so it works verbatim for Sanders' local notion. -/
theorem weighted_rudin_exp_ineq
    (mu : G → ℝ) (K : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x)
    (hDelta : IsWeightedDissociated mu K Delta)
    (c : AddChar G ℂ → ℂ) :
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
      exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (x : G) :
      exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
    calc
      exp ((∑ psi ∈ Delta, c psi * psi x).re) =
          ∏ psi ∈ Delta, exp ((c psi * psi x).re) := by
            simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi ∈ Delta,
          (cosh ‖c psi * psi x‖ +
            ((c psi * psi x) / ‖c psi * psi x‖).re *
              sinh ‖c psi * psi x‖) := by
        gcongr with psi hpsi
        exact hexp _
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ +
            (u psi * (c psi * psi x) / (u psi * ↑‖c psi‖)).re *
              sinh ‖c psi‖) := by
        apply prod_congr rfl
        intro psi hpsi
        rw [norm_mul, AddChar.norm_apply, mul_one,
          mul_div_mul_left _ _ (hu0 psi)]
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
        apply prod_congr rfl
        intro psi hpsi
        obtain hc | hc := eq_or_ne (c psi) 0
        · simp [hc]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hc,
          ← Complex.re_mul_ofReal, mul_right_comm]
  let q : AddChar G ℂ → ℝ := fun psi ↦ sinh ‖c psi‖ / cosh ‖c psi‖
  let v : AddChar G ℂ → ℂ := fun psi ↦ (q psi : ℂ) * u psi
  have hfactor (x : G) :
      (∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re)) =
        (∏ psi ∈ Delta, cosh ‖c psi‖) *
          (∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
    rw [← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro psi hpsi
    have hcosh : cosh ‖c psi‖ ≠ 0 := ne_of_gt (cosh_pos _)
    have hsinh_re :
        (u psi * (sinh ‖c psi‖ : ℂ) * psi x).re =
          sinh ‖c psi‖ * (u psi * psi x).re := by
      rw [show u psi * (sinh ‖c psi‖ : ℂ) * psi x =
          (sinh ‖c psi‖ : ℂ) * (u psi * psi x) by ring]
      exact Complex.re_ofReal_mul _ _
    have hv_re : (v psi * psi x).re = q psi * (u psi * psi x).re := by
      rw [show v psi * psi x = (q psi : ℂ) * (u psi * psi x) by
        simp [v]; ring]
      exact Complex.re_ofReal_mul _ _
    rw [hsinh_re, hv_re]
    dsimp [q]
    field_simp
  calc
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∑ x : G, mu x * ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmu x)
    _ = (∏ psi ∈ Delta, cosh ‖c psi‖) *
        (∑ x : G, mu x *
          ∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [hfactor]
      ring
    _ ≤ (∏ psi ∈ Delta, cosh ‖c psi‖) * exp K := by
      gcongr
      apply hDelta v
      intro psi hpsi
      have hq : |q psi| ≤ 1 := by
        simpa [q, Real.tanh_eq_sinh_div_cosh] using (Real.abs_tanh_lt_one ‖c psi‖).le
      simpa [v, norm_mul, hu psi, Complex.norm_real, Real.norm_eq_abs] using hq
    _ ≤ exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) * exp K := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        ∏ psi ∈ Delta, cosh ‖c psi‖ ≤
            ∏ psi ∈ Delta, exp (‖c psi‖ ^ 2 / 2) := by
          gcongr with psi hpsi
          exact cosh_le_exp_half_sq _
        _ = exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
          simp_rw [← exp_sum, ← sum_div]
    _ = exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
      rw [← exp_add]
      congr 1
      ring

/-! ## The relative logarithmic dimension bound -/

/-- A measure-dissociated subset of the relative large spectrum has
cardinality controlled by the density relative to that measure.  Crucially,
the right side contains no occurrence of `Fintype.card G`.

The explicit constant is deliberately coarse.  In the application `K = 1`
and `f` is an indicator, so `a = |X|/|B|`. -/
theorem card_weightedDissociated_relativeLargeSpectrum_le
    (mu f : G → ℝ) (K eta : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (heta : 0 < eta)
    (hDelta : IsWeightedDissociated mu K Delta)
    (hsub : Delta ⊆ relativeLargeSpectrum mu f eta)
    (hmass : 0 < ∑ x : G, f x * mu x) :
    (Delta.card : ℝ) ≤
      2 * (K + log ((∑ x : G, f x * mu x)⁻¹)) / eta ^ 2 := by
  let a : ℝ := ∑ x : G, f x * mu x
  have ha : 0 < a := by simpa [a] using hmass
  let spec : AddChar G ℂ → ℂ := fun psi ↦
    ∑ x : G, (f x * mu x : ℝ) * psi x
  choose u hu huspec using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spec psi)
  let c : AddChar G ℂ → ℂ := fun psi ↦ (eta : ℂ) * u psi
  let P : G → ℝ := fun x ↦ (∑ psi ∈ Delta, c psi * psi x).re
  have hc_norm (psi : AddChar G ℂ) : ‖c psi‖ ^ 2 = eta ^ 2 := by
    simp [c, hu, abs_of_pos heta]
  have hc_sq : ∑ psi ∈ Delta, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm]
    simp
    ring
  have hcomplex :
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
    calc
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
          ∑ psi ∈ Delta,
            c psi * ∑ x : G, ((f x * mu x : ℝ) : ℂ) * psi x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro psi hpsi
        apply sum_congr rfl
        intro x hx
        ring
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spec psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        dsimp [c, spec]
        rw [mul_assoc, ← huspec]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
        rw [Finset.mul_sum]
  have hmeanP :
      ∑ x : G, f x * mu x * P x =
        eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
    have hre := congrArg Complex.re hcomplex
    calc
      ∑ x : G, f x * mu x * P x =
          (∑ x : G, ((f x * mu x : ℝ) : ℂ) *
            (∑ psi ∈ Delta, c psi * psi x)).re := by
        simp [P, Complex.re_sum, Complex.mul_re]
      _ = ((eta : ℂ) *
          ∑ psi ∈ Delta, (‖spec psi‖ : ℂ)).re := hre
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by simp
  have hmean_lower :
      eta ^ 2 * a * Delta.card ≤ ∑ x : G, f x * mu x * P x := by
    rw [hmeanP]
    calc
      eta ^ 2 * a * (Delta.card : ℝ) =
          ∑ psi ∈ Delta, eta * (eta * a) := by
        simp
        ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spec psi‖ := by
        gcongr with psi hpsi
        have hs := mem_relativeLargeSpectrum.mp (hsub hpsi)
        simpa [a, spec] using hs
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
        rw [Finset.mul_sum]
  let w : G → ℝ := fun x ↦ f x * mu x / a
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (mul_nonneg (hf0 x) (hmu x)) ha.le
  have hw_sum : ∑ x : G, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    dsimp [a]
    exact div_self ha.ne'
  have hmean_w : eta ^ 2 * Delta.card ≤ ∑ x : G, w x * P x := by
    calc
      eta ^ 2 * (Delta.card : ℝ) ≤
          (∑ x : G, f x * mu x * P x) / a := by
        rw [le_div_iff₀ ha]
        calc
          eta ^ 2 * (Delta.card : ℝ) * a =
              eta ^ 2 * a * (Delta.card : ℝ) := by ring
          _ ≤ _ := hmean_lower
      _ = ∑ x : G, w x * P x := by
        dsimp [w]
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro x hx
        ring
  have hJensen :
      exp (eta ^ 2 * Delta.card) ≤
        ∑ x : G, w x * exp (P x) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (∑ x : G, w x * P x) := by
        exact Real.exp_le_exp.mpr hmean_w
      _ ≤ _ := exp_weightedAverage_le_weightedAverage_exp w hw0 hw_sum P
  have hweighted_le :
      ∑ x : G, w x * exp (P x) ≤
        a⁻¹ * ∑ x : G, mu x * exp (P x) := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x hx
    rw [div_eq_inv_mul]
    calc
      a⁻¹ * (f x * mu x) * exp (P x) ≤
          a⁻¹ * (1 * mu x) * exp (P x) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact mul_le_mul_of_nonneg_right (hf1 x) (hmu x)
      _ = a⁻¹ * (mu x * exp (P x)) := by ring
  have hRudin :
      ∑ x : G, mu x * exp (P x) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    have hr := weighted_rudin_exp_ineq mu K Delta hmu hDelta c
    simpa [P, hc_sq] using hr
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2) :=
    hJensen.trans (hweighted_le.trans
      (mul_le_mul_of_nonneg_left hRudin (inv_nonneg.mpr ha.le)))
  have hmul :
      a * exp (eta ^ 2 * Delta.card) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    calc
      a * exp (eta ^ 2 * Delta.card) ≤
          a * (a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2)) := by
        gcongr
      _ = exp (K + eta ^ 2 * Delta.card / 2) := by
        field_simp
  have hlinear :
      log a + eta ^ 2 * Delta.card ≤
        K + eta ^ 2 * Delta.card / 2 := by
    rw [← exp_log ha, ← exp_add] at hmul
    exact Real.exp_le_exp.mp hmul
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  rw [log_inv]
  nlinarith

/-- Constant-on-a-set specialization of the relative dimension bound.  The
parameter `R` is any upper bound for the reciprocal weighted mass of `X`;
in the smoothed-Bohr application it is `2 * |B| / |X|`. -/
theorem card_weightedDissociated_finsetIndicator_le
    [DecidableEq G] (B X : Finset G) (hXB : X ⊆ B) (hX : X.Nonempty)
    (w : G → ℝ) (c R eta : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∈ B, w x = c)
    (hc : 0 < c) (hR : (c * X.card)⁻¹ ≤ R)
    (heta : 0 < eta) (Delta : Finset (AddChar G ℂ))
    (hDelta : IsWeightedDissociated w 1 Delta)
    (hsub : Delta ⊆ Chang.largeSpectrum X eta) :
    (Delta.card : ℝ) ≤ 2 * (1 + log R) / eta ^ 2 := by
  have hmass_eq :
      ∑ x : G, finsetIndicator X x * w x = c * X.card :=
    RelativeSpectrumBridge.sum_finsetIndicator_mul_eq_const_mul_card hXB hw
  have hmass : 0 < ∑ x : G, finsetIndicator X x * w x := by
    rw [hmass_eq]
    have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have hsub' : Delta ⊆
      relativeLargeSpectrum w (finsetIndicator X) eta := by
    intro psi hpsi
    exact (RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
      hXB hw hc eta psi).2 (hsub hpsi)
  have hdim := card_weightedDissociated_relativeLargeSpectrum_le
    w (finsetIndicator X) 1 eta Delta hw0
    (by intro x; unfold finsetIndicator; split <;> norm_num)
    (by intro x; unfold finsetIndicator; split <;> norm_num)
    heta hDelta hsub' hmass
  have hmassInv :
      ((∑ x : G, finsetIndicator X x * w x)⁻¹) ≤ R := by
    simpa [hmass_eq] using hR
  have hlog :
      log ((∑ x : G, finsetIndicator X x * w x)⁻¹) ≤ log R :=
    Real.log_le_log (inv_pos.mpr hmass) hmassInv
  calc
    (Delta.card : ℝ) ≤
        2 * (1 + log ((∑ x : G, finsetIndicator X x * w x)⁻¹)) /
          eta ^ 2 := by simpa using hdim
    _ ≤ 2 * (1 + log R) / eta ^ 2 := by
      gcongr

/-- The finite capped-maximality step used by the local Chang argument. -/
theorem exists_capped_addDissociatedMod
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hneg : ∀ s ∈ S, -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  classical
  obtain ⟨Delta, hDeltaT, hDeltaMod, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hneg
  have hDeltaCard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_not_ge hnot
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaDim := hdim Gamma (hGammaDelta.trans hDeltaT)
      (hDeltaMod.mono hGammaDelta) (by simpa [hGammaCard])
    rw [hGammaCard] at hGammaDim
    exact (not_le_of_gt hDk) hGammaDim
  exact ⟨Delta, hDeltaT, hdim Delta hDeltaT hDeltaMod hDeltaCard, hcover⟩

/-! ## The unconditional local selector -/

/-- The local logarithmic dimension parameter.  Only the density of `X`
inside `B` occurs; there is no ambient-group cardinality. -/
def localChangDimension (B : BohrData G) (X : Finset G) (eta : ℝ) : ℝ :=
  2 * (1 + log (2 * (B.carrier.card : ℝ) / X.card)) / eta ^ 2

/-- The cap used to remove the apparent circularity in the smoothing
argument. -/
def localChangCap (B : BohrData G) (X : Finset G) (eta : ℝ) : ℕ :=
  ⌈localChangDimension B X eta⌉₊ + 1

/-- An explicit scale at which Bourgain's regular-dilate lemma is applied. -/
def localChangBaseScale (B : BohrData G) (X : Finset G)
    (eta : ℝ) : NNReal :=
  (100 * ((max B.rank 1 : ℕ) : NNReal) *
    (((2 * localChangCap B X eta + 1 : ℕ) : NNReal)))⁻¹

/-- **Relative Chang--Sanders selector.**  If `X` is nonempty inside a
rank-regular Bohr set `B`, then its `eta`-large spectrum is covered by the
signed span of at most

`2 * (1 + log (2 * |B| / |X|)) / eta^2`

new characters, modulo the half-large spectrum of an explicit regular
dilate of `B`.  In particular the logarithm contains no ambient-group
cardinality. -/
theorem exists_relativeLargeSpectrum_cover
    [DecidableEq G] (B : BohrData G) (hBreg : B.IsRankRegular)
    (X : Finset G) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ rho : NNReal, ∃ C : BohrData G,
      ∃ Delta : Finset (AddChar G ℂ),
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.dilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        ∀ psi ∈ Chang.largeSpectrum X eta,
          ∃ z ∈ Delta.addSpan,
            ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s := by
  classical
  let D : ℝ := localChangDimension B X eta
  let k : ℕ := localChangCap B X eta
  let d : ℕ := max B.rank 1
  let a : NNReal := localChangBaseScale B X eta
  obtain ⟨rho, hrhoHalf, hrhoOne, hregular⟩ :=
    (B.dilate a).exists_rankRegular_dilate
  let tau : NNReal := rho * a
  let C : BohrData G := B.dilate tau
  have hCreg : C.IsRankRegular := by
    simpa [C, tau] using hregular
  have hd : 0 < d := by simp [d]
  have hk : 0 < k := by simp [k, localChangCap]
  have ha : a =
      (100 * (d : NNReal) * (((2 * k + 1 : ℕ) : NNReal)))⁻¹ := by
    simp [a, localChangBaseScale, d, k]
  have hsmall : (((2 * k : ℕ) : NNReal) * tau) ≤
      1 / (100 * (d : NNReal)) := by
    have hkden : (0 : NNReal) < (((2 * k + 1 : ℕ) : NNReal)) := by positivity
    have hdb : (0 : NNReal) < 100 * (d : NNReal) := by positivity
    calc
      (((2 * k : ℕ) : NNReal) * tau) =
          ((2 * k : ℕ) : NNReal) * (rho * a) := rfl
      _ ≤ ((2 * k : ℕ) : NNReal) * (1 * a) := by gcongr
      _ = (((2 * k : ℕ) : NNReal) /
          (((2 * k + 1 : ℕ) : NNReal))) /
            (100 * (d : NNReal)) := by rw [ha]; field_simp
      _ ≤ 1 / (100 * (d : NNReal)) := by
        gcongr
        exact (div_le_one hkden).2 (by
          exact_mod_cast Nat.le_add_right (2 * k) 1)
  let T : Finset (AddChar G ℂ) := Chang.largeSpectrum X eta
  let S : Finset (AddChar G ℂ) :=
    Chang.largeSpectrum C.carrier (1 / 2)
  let w : G → ℝ := Erdos140.bohrSmoothingMeasure B tau (2 * k)
  let outer : Finset G :=
    (B.dilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier
  let c : ℝ := (outer.card : ℝ)⁻¹
  let R : ℝ := 2 * (B.carrier.card : ℝ) / X.card
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact Erdos140.bohrSmoothingMeasure_nonneg B tau (2 * k) x
  have hw1 : ∑ x : G, w x = 1 := by
    exact Erdos140.sum_bohrSmoothingMeasure B tau (2 * k)
  have hwconst : ∀ x ∈ B.carrier, w x = c := by
    intro x hx
    simpa [w, c, outer] using
      (Erdos140.bohrSmoothingMeasure_apply_of_mem B tau (2 * k) hx)
  have hOuterCard : outer.card ≤ 2 * B.carrier.card := by
    simpa [outer, d] using
      (Erdos140.card_dilate_one_add_le_two_mul hBreg (2 * k) hsmall)
  have hOuterPos : 0 < outer.card := by
    exact outer.card_pos.mpr (by
      simpa [outer] using
        (B.dilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier_nonempty)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hR : (c * X.card)⁻¹ ≤ R := by
    have hOr : (0 : ℝ) < outer.card := by exact_mod_cast hOuterPos
    have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hOr' : (outer.card : ℝ) ≤ 2 * B.carrier.card := by
      exact_mod_cast hOuterCard
    calc
      (c * (X.card : ℝ))⁻¹ = (outer.card : ℝ) / X.card := by
        dsimp [c]
        field_simp
      _ ≤ (2 * B.carrier.card : ℝ) / X.card :=
        (div_le_div_iff_of_pos_right hXr).2 hOr'
      _ = R := by simp [R]
  have hzero : (0 : AddChar G ℂ) ∈ S := by
    exact zero_mem_chang_largeSpectrum_half C.carrier
  have hneg : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    exact neg_mem_chang_largeSpectrum hs
  have hDk : D < (k : ℝ) := by
    calc
      D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
      _ < ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self ⌈D⌉₊
      _ = (k : ℝ) := by simp [k, localChangCap, D]
  have hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D := by
    intro Gamma hGammaT hGammaMod hGammaCard
    have hq : ∀ psi, psi ∉ S →
        ‖Erdos140.massCoeff w psi‖ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
      intro psi hpsi
      calc
        ‖Erdos140.massCoeff w psi‖ ≤
            ‖Erdos140.massCoeff
              (normalizedIndicator (B.dilate tau).carrier) psi‖ ^ (2 * k) := by
          exact Erdos140.norm_massCoeff_bohrSmoothingMeasure_le
            B tau (2 * k) psi
        _ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
          gcongr
          exact (Erdos140.norm_massCoeff_normalizedIndicator_lt_half_of_not_mem_largeSpectrum
            (B.dilate tau) psi (by simpa [S, C] using hpsi)).le
    have hweighted : IsWeightedDissociated w 1 Gamma := by
      apply hGammaMod.isWeightedDissociated_of_le_quarter_pow
        hw0 hw1 (by positivity) hq hGammaCard
      rw [pow_mul]
      norm_num
    have hcard := card_weightedDissociated_finsetIndicator_le
      B.carrier X hXB hX w c R eta hw0 hwconst hc hR heta Gamma
        hweighted (by simpa [T] using hGammaT)
    simpa [D, localChangDimension, R] using hcard
  obtain ⟨Delta, hDeltaT, hDeltaCard, hcover⟩ :=
    exists_capped_addDissociatedMod S T hzero hneg D k hDk hdim
  refine ⟨rho, C, Delta, hrhoHalf, hrhoOne, ?_, hCreg, ?_, ?_, ?_⟩
  · simp [C, tau, a]
  · simpa [D] using hDeltaCard
  · simpa [T] using hDeltaT
  · simpa [T, S] using hcover

end RelativeChangSanders

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/LocalSpectrum.lean` -/

section
/-!
# Large spectra and finite Bohr data

This file supplies the change of models between Mathlib's complex characters
`AddChar G ℂ` and the additive-circle characters used by `Erdos140.BohrData`.
-/

open _root_.Finset _root_.Function _root_.Real
open scoped BigOperators _root_.NNReal

namespace LocalSpectrum

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- The additive-circle character corresponding to a complex character of a
finite abelian group. -/
noncomputable def circleLogCharacter (psi : AddChar G ℂ) : AddCharacter G := by
  let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
  exact
    { toFun := fun x ↦ e.symm ((AddChar.circleEquivComplex.symm psi) x)
      map_zero' := by
        apply e.injective
        simp [e, AddCircle.homeomorphCircle_apply]
      map_add' := by
        intro x y
        apply e.injective
        rw [e.apply_symm_apply]
        rw [show e (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) =
            AddCircle.toCircle (e.symm ((AddChar.circleEquivComplex.symm psi) x) +
              e.symm ((AddChar.circleEquivComplex.symm psi) y)) by
              exact AddCircle.homeomorphCircle_apply _ _]
        rw [AddCircle.toCircle_add]
        rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0),
          e.apply_symm_apply]
        rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0),
          e.apply_symm_apply]
        exact AddChar.map_add_eq_mul _ _ _ }

theorem toCircle_circleLogCharacter (psi : AddChar G ℂ) (x : G) :
    AddCircle.toCircle (circleLogCharacter psi x) =
      (AddChar.circleEquivComplex.symm psi) x := by
  rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
  simp [circleLogCharacter]

theorem coe_toCircle_circleLogCharacter (psi : AddChar G ℂ) (x : G) :
    (AddCircle.toCircle (circleLogCharacter psi x) : ℂ) = psi x := by
  rw [toCircle_circleLogCharacter]
  exact DFunLike.congr_fun (AddChar.circleEquivComplex.apply_symm_apply psi) x

theorem circleLogCharacter_injective :
    Function.Injective (circleLogCharacter (G := G)) := by
  intro psi chi h
  ext x
  have hx := DFunLike.congr_fun h x
  have hh := congrArg (fun z : AddCircle (1 : ℝ) ↦ (AddCircle.toCircle z : ℂ)) hx
  simpa only [coe_toCircle_circleLogCharacter] using hh

/-- Conversion of complex characters to additive-circle characters is an
additive homomorphism. -/
noncomputable def circleLogHom :
    AddChar G ℂ →+ AddCharacter G where
  toFun := circleLogCharacter
  map_zero' := by
    ext x
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simp [coe_toCircle_circleLogCharacter]
  map_add' psi chi := by
    ext x
    apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
    apply Subtype.ext
    simp [coe_toCircle_circleLogCharacter, AddCircle.toCircle_add,
      AddChar.add_apply]

@[simp] theorem circleLogHom_apply (psi : AddChar G ℂ) :
    circleLogHom psi = circleLogCharacter psi := rfl

/-! ## The Bohr datum generated by a character basis -/

/-- The Bohr datum with frequency basis `Delta` and constant arc width `r`. -/
noncomputable def basisBohrData (Delta : Finset (AddChar G ℂ)) (r : ℝ≥0) :
    BohrData G where
  freq := Delta.image circleLogCharacter
  width := fun _ ↦ r

@[simp] theorem basisBohrData_rank (Delta : Finset (AddChar G ℂ)) (r : ℝ≥0) :
    (basisBohrData Delta r).rank = Delta.card := by
  classical
  rw [BohrData.rank, basisBohrData]
  exact Finset.card_image_iff.mpr circleLogCharacter_injective.injOn

@[simp] theorem basisBohrData_width (Delta : Finset (AddChar G ℂ)) (r : ℝ≥0)
    (gamma : AddCharacter G) :
    (basisBohrData Delta r).width gamma = r := rfl

/-- A point of the basis Bohr set approximately annihilates every character
in the `{0,1,-1}`-span of the basis. -/
theorem norm_circleLogCharacter_le_card_mul_of_mem_addSpan
    {Delta : Finset (AddChar G ℂ)} {r : ℝ≥0} {psi : AddChar G ℂ} {x : G}
    (hx : x ∈ (basisBohrData Delta r).carrier)
    (hpsi : psi ∈ Delta.addSpan) :
    ‖circleLogCharacter psi x‖ ≤ (Delta.card : ℝ) * (r : ℝ) := by
  classical
  rw [Finset.mem_addSpan] at hpsi
  obtain ⟨epsilon, hepsilon, hsum⟩ := hpsi
  have hsumLog :
      ∑ gamma ∈ Delta, epsilon gamma • circleLogCharacter gamma =
        circleLogCharacter psi := by
    change ∑ gamma ∈ Delta, epsilon gamma • circleLogHom gamma = circleLogHom psi
    calc
      ∑ gamma ∈ Delta, epsilon gamma • circleLogHom gamma =
          ∑ gamma ∈ Delta, circleLogHom (epsilon gamma • gamma) := by
            apply sum_congr rfl
            intro gamma hgamma
            exact (map_zsmul circleLogHom (epsilon gamma) gamma).symm
      _ = circleLogHom (∑ gamma ∈ Delta, epsilon gamma • gamma) := by
        exact (map_sum circleLogHom (fun gamma ↦ epsilon gamma • gamma) Delta).symm
      _ = circleLogHom psi := congrArg circleLogHom hsum
  have hsumApply :
      (∑ gamma ∈ Delta, epsilon gamma • circleLogCharacter gamma) x =
        ∑ gamma ∈ Delta, (epsilon gamma • circleLogCharacter gamma) x := by
    induction Delta using Finset.induction_on with
    | empty => simp
    | @insert gamma Delta hgamma ih => simp [hgamma, ih]
  rw [← hsumLog, hsumApply]
  calc
    ‖∑ gamma ∈ Delta, (epsilon gamma • circleLogCharacter gamma) x‖ ≤
        ∑ gamma ∈ Delta, ‖(epsilon gamma • circleLogCharacter gamma) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _gamma ∈ Delta, (r : ℝ) := by
      apply sum_le_sum
      intro gamma hgamma
      have hfreq : circleLogCharacter gamma ∈ (basisBohrData Delta r).freq := by
        exact Finset.mem_image.mpr ⟨gamma, hgamma, rfl⟩
      have hwidth := (BohrData.mem_carrier _ _).mp hx
        (circleLogCharacter gamma) hfreq
      have hw : ‖circleLogCharacter gamma x‖ ≤ (r : ℝ) := by
        simpa only [basisBohrData_width] using hwidth
      rcases hepsilon gamma with hneg | hzero | hone
      · simpa [hneg] using hw
      · simp [hzero]
      · simpa [hone] using hw
    _ = (Delta.card : ℝ) * (r : ℝ) := by simp

/-! ## Adjoining a basis to existing Bohr data -/

/-- Intersect a dilate of existing Bohr data with the constant-width Bohr
datum generated by `Delta`.  Frequencies occurring in both data receive the
minimum of the two widths. -/
noncomputable def adjoinBasis (B : BohrData G)
    (Delta : Finset (AddChar G ℂ)) (kappa r : ℝ≥0) : BohrData G := by
  classical
  let newFreq := Delta.image circleLogCharacter
  exact
    { freq := B.freq ∪ newFreq
      width := fun gamma ↦
        if gamma ∈ B.freq then
          if gamma ∈ newFreq then min (kappa * B.width gamma) r
          else kappa * B.width gamma
        else r }

theorem adjoinBasis_rank_le (B : BohrData G)
    (Delta : Finset (AddChar G ℂ)) (kappa r : ℝ≥0) :
    (adjoinBasis B Delta kappa r).rank ≤ B.rank + Delta.card := by
  classical
  rw [BohrData.rank, BohrData.rank, adjoinBasis]
  exact (Finset.card_union_le _ _).trans_eq (by
    rw [Finset.card_image_iff.mpr circleLogCharacter_injective.injOn])

theorem adjoinBasis_carrier_subset_dilate (B : BohrData G)
    (Delta : Finset (AddChar G ℂ)) (kappa r : ℝ≥0) :
    (adjoinBasis B Delta kappa r).carrier ⊆ (B.dilate kappa).carrier := by
  classical
  intro x hx
  rw [BohrData.mem_carrier] at hx ⊢
  intro gamma hgamma
  have hgammaB : gamma ∈ B.freq := by simpa using hgamma
  have hUnion : gamma ∈ B.freq ∪ Delta.image circleLogCharacter :=
    Finset.mem_union_left _ hgammaB
  have hbound := hx gamma (by simpa [adjoinBasis] using hUnion)
  by_cases hnew : gamma ∈ Delta.image circleLogCharacter
  · change ‖gamma x‖ ≤
      (((if gamma ∈ B.freq then
          if gamma ∈ Delta.image circleLogCharacter then
            min (kappa * B.width gamma) r else kappa * B.width gamma
        else r) : ℝ≥0) : ℝ) at hbound
    rw [if_pos hgammaB, if_pos hnew] at hbound
    simpa only [BohrData.width_dilate, NNReal.coe_mul] using
      hbound.trans (by exact_mod_cast (min_le_left (kappa * B.width gamma) r))
  · change ‖gamma x‖ ≤
      (((if gamma ∈ B.freq then
          if gamma ∈ Delta.image circleLogCharacter then
            min (kappa * B.width gamma) r else kappa * B.width gamma
        else r) : ℝ≥0) : ℝ) at hbound
    rw [if_pos hgammaB, if_neg hnew] at hbound
    simpa only [BohrData.width_dilate, NNReal.coe_mul] using hbound

theorem adjoinBasis_carrier_subset_basisBohrData (B : BohrData G)
    (Delta : Finset (AddChar G ℂ)) (kappa r : ℝ≥0) :
    (adjoinBasis B Delta kappa r).carrier ⊆ (basisBohrData Delta r).carrier := by
  classical
  intro x hx
  rw [BohrData.mem_carrier] at hx ⊢
  intro gamma hgamma
  rw [basisBohrData_width]
  obtain ⟨psi, hpsi, rfl⟩ := Finset.mem_image.mp hgamma
  have hnew : circleLogCharacter psi ∈ Delta.image circleLogCharacter :=
    Finset.mem_image.mpr ⟨psi, hpsi, rfl⟩
  have hUnion : circleLogCharacter psi ∈ B.freq ∪ Delta.image circleLogCharacter :=
    Finset.mem_union_right _ hnew
  have hbound := hx (circleLogCharacter psi) (by simpa [adjoinBasis] using hUnion)
  by_cases hold : circleLogCharacter psi ∈ B.freq
  · change ‖circleLogCharacter psi x‖ ≤
      (((if circleLogCharacter psi ∈ B.freq then
          if circleLogCharacter psi ∈ Delta.image circleLogCharacter then
            min (kappa * B.width (circleLogCharacter psi)) r
          else kappa * B.width (circleLogCharacter psi)
        else r) : ℝ≥0) : ℝ) at hbound
    rw [if_pos hold, if_pos hnew] at hbound
    exact hbound.trans (by
      exact_mod_cast (min_le_right (kappa * B.width (circleLogCharacter psi)) r))
  · change ‖circleLogCharacter psi x‖ ≤
      (((if circleLogCharacter psi ∈ B.freq then
          if circleLogCharacter psi ∈ Delta.image circleLogCharacter then
            min (kappa * B.width (circleLogCharacter psi)) r
          else kappa * B.width (circleLogCharacter psi)
        else r) : ℝ≥0) : ℝ) at hbound
    rw [if_neg hold] at hbound
    exact hbound

/-- The adjoined datum is subordinate to `B.dilate kappa` and annihilates
the whole signed span of the new basis. -/
theorem norm_circleLogCharacter_le_card_mul_of_mem_adjoinBasis
    (B : BohrData G) {Delta : Finset (AddChar G ℂ)} {kappa r : ℝ≥0}
    {psi : AddChar G ℂ} {x : G}
    (hx : x ∈ (adjoinBasis B Delta kappa r).carrier)
    (hpsi : psi ∈ Delta.addSpan) :
    ‖circleLogCharacter psi x‖ ≤ (Delta.card : ℝ) * (r : ℝ) :=
  norm_circleLogCharacter_le_card_mul_of_mem_addSpan
    (adjoinBasis_carrier_subset_basisBohrData B Delta kappa r hx) hpsi

/-! ## Arc norm versus chord norm -/

/-- On a short arc, chord length is at most four pi times additive-circle
norm.  The coarse factor four lets us use Mathlib's elementary local estimate
for the complex exponential. -/
theorem norm_one_sub_character_le_four_pi_mul
    (psi : AddChar G ℂ) (x : G)
    (hshort : ‖circleLogCharacter psi x‖ ≤ (2 * Real.pi)⁻¹) :
    ‖1 - psi x‖ ≤ 4 * Real.pi * ‖circleLogCharacter psi x‖ := by
  let a : ℝ := AddCircle.equivIoc (1 : ℝ) (-1 / 2) (circleLogCharacter psi x)
  have ha_mem : a ∈ Set.Ioc (-1 / 2) (-1 / 2 + 1) :=
    (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (circleLogCharacter psi x)).property
  have ha_abs : |a| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [ha_mem.1, ha_mem.2]
  have hcoe : (a : AddCircle (1 : ℝ)) = circleLogCharacter psi x := by
    exact AddCircle.coe_equivIoc
  have hnorm_a : ‖circleLogCharacter psi x‖ = |a| := by
    rw [← hcoe]
    exact (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using ha_abs)
  have hnorm_scalar : ‖(2 * Real.pi * a : ℂ)‖ = 2 * Real.pi * |a| := by
    simp [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg Real.pi_nonneg]
  have harg : ‖(2 * Real.pi * a : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, hnorm_scalar, ← hnorm_a]
    have hpi : 0 < 2 * Real.pi := by positivity
    calc
      2 * Real.pi * ‖circleLogCharacter psi x‖ ≤
          2 * Real.pi * (2 * Real.pi)⁻¹ :=
        mul_le_mul_of_nonneg_left hshort hpi.le
      _ = 1 := by field_simp
  have hexp := Complex.norm_exp_sub_one_le harg
  have heval : psi x = Complex.exp ((2 * Real.pi * a : ℂ) * Complex.I) := by
    rw [← coe_toCircle_circleLogCharacter psi x, ← hcoe]
    simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1
    push_cast
    field_simp
  rw [heval, norm_sub_rev]
  calc
    ‖Complex.exp ((2 * Real.pi * a : ℂ) * Complex.I) - 1‖
        ≤ 2 * ‖(2 * Real.pi * a : ℂ) * Complex.I‖ := hexp
    _ = 4 * Real.pi * ‖circleLogCharacter psi x‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, hnorm_scalar, hnorm_a]
      ring

/-- Chord-length version of signed-span annihilation on an adjoined Bohr
datum. -/
theorem norm_one_sub_character_le_of_mem_adjoinBasis
    (B : BohrData G) {Delta : Finset (AddChar G ℂ)} {kappa r : ℝ≥0}
    {psi : AddChar G ℂ} {x : G}
    (hsmall : (Delta.card : ℝ) * (r : ℝ) ≤ (2 * Real.pi)⁻¹)
    (hx : x ∈ (adjoinBasis B Delta kappa r).carrier)
    (hpsi : psi ∈ Delta.addSpan) :
    ‖1 - psi x‖ ≤ 4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) := by
  have harc := norm_circleLogCharacter_le_card_mul_of_mem_adjoinBasis
    B hx hpsi
  calc
    ‖1 - psi x‖ ≤ 4 * Real.pi * ‖circleLogCharacter psi x‖ :=
      norm_one_sub_character_le_four_pi_mul psi x (harc.trans hsmall)
    _ ≤ 4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) :=
      mul_le_mul_of_nonneg_left harc (by positivity)

/-- If a family of characters is covered by the signed span of `Delta` plus
a residual family, then the adjoined datum annihilates the covered family up
to the sum of the two errors.  This is the algebraic assembly step in the
relative Chang--Sanders argument. -/
theorem norm_one_sub_character_le_of_addSpan_add_cover
    (B : BohrData G) {Delta Q S : Finset (AddChar G ℂ)} {kappa r : ℝ≥0}
    {beta : ℝ} {x : G}
    (hsmall : (Delta.card : ℝ) * (r : ℝ) ≤ (2 * Real.pi)⁻¹)
    (hx : x ∈ (adjoinBasis B Delta kappa r).carrier)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s)
    (hresidual : ∀ s ∈ S, ‖1 - s x‖ ≤ beta) :
    ∀ psi ∈ Q,
      ‖1 - psi x‖ ≤ 4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) + beta := by
  intro psi hpsi
  obtain ⟨z, hz, s, hs, rfl⟩ := hcover psi hpsi
  have hzbound :
      ‖1 - z x‖ ≤ 4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) :=
    norm_one_sub_character_le_of_mem_adjoinBasis B hsmall hx hz
  calc
    ‖1 - (z + s) x‖ = ‖(1 - z x) + z x * (1 - s x)‖ := by
      rw [AddChar.add_apply]
      congr 1
      ring
    _ ≤ ‖1 - z x‖ + ‖z x * (1 - s x)‖ := norm_add_le _ _
    _ = ‖1 - z x‖ + ‖1 - s x‖ := by
      rw [norm_mul, AddChar.norm_apply, one_mul]
    _ ≤ 4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) + beta :=
      add_le_add hzbound (hresidual s hs)

/-- Relative-cover specialization for a rank-regular Bohr datum.  The
residual set is the half-large spectrum of the old carrier, so membership in
the old `sigma`-dilate supplies its phase error.  This is the geometric half
of the local Chang--Sanders theorem. -/
theorem norm_one_sub_character_le_of_localSpectrum_cover
    (C : BohrData G) (hreg : C.IsRankRegular)
    {Delta Q : Finset (AddChar G ℂ)} {sigma r : ℝ≥0}
    (hsigma : sigma ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * (r : ℝ) ≤ (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s) :
    ∀ x ∈ (adjoinBasis C Delta sigma r).carrier, ∀ psi ∈ Q,
      ‖1 - psi x‖ ≤
        4 * Real.pi * ((Delta.card : ℝ) * (r : ℝ)) +
          400 * ((max C.rank 1 : ℕ) : ℝ) * (sigma : ℝ) := by
  intro x hx
  apply norm_one_sub_character_le_of_addSpan_add_cover
    C hsmall hx hcover
  intro s hs
  exact Erdos140.norm_one_sub_le_of_mem_largeSpectrum_half
    hreg hsigma hs (adjoinBasis_carrier_subset_dilate C Delta sigma r hx)

/-! ## The relative Chang--Sanders Bohr theorem -/

/-! ## Global Chang-to-Bohr corollary -/

end LocalSpectrum

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RelativeBohrVolume.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Relative volume after adjoining frequencies

The usual ambient Bohr-volume estimate is not sufficient when new
frequencies are adjoined to a small Bohr set: it loses the relative density
of the old Bohr set in the whole group.  This file proves the required local
estimate directly.

If `S` is contained in `B_κ`, partition `S` by the `m`-cell signatures of a
finite family `Delta` of characters.  One signature fibre has relative size
at least `m ^ (-|Delta|)`.  After translating that fibre by one of its points,
all differences lie in `B_(κ+κ)` and in the width-`1/m` Bohr set generated by
`Delta`.  Thus

`|S| ≤ m^|Delta| |adjoinBasis B Delta (κ+κ) (1/m)|`.

The argument partitions the *given subset* `S`; in particular, no ambient
`|G|` bound enters the proof.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal

namespace RelativeBohrVolume

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

open BohrData LocalSpectrum

/-! ## Equal-length cells on the additive circle

The canonical representative of an element of `R/Z` lies in `[-1/2,1/2)`.
After translating this interval to `[0,1)` and multiplying by `m`, its
natural floor is an element of `Fin m`.
-/

/-- The equal-length `m`-cell containing a circle point. -/
def circleCell (m : Nat) (hm : 0 < m) (z : AddCircle (1 : Real)) : Fin m := by
  have hnonneg : 0 ≤ (circleRep z + 1 / 2) * (m : Real) := by
    have hz := (circleRep_mem z).1
    have hmR : (0 : Real) ≤ m := by positivity
    exact mul_nonneg (by linarith) hmR
  refine ⟨⌊(circleRep z + 1 / 2) * m⌋₊, (Nat.floor_lt hnonneg).2 ?_⟩
  have hz : circleRep z + 1 / 2 < 1 := by
    linarith [(circleRep_mem z).2]
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  exact (mul_lt_mul_of_pos_right hz hmR).trans_eq (one_mul (m : Real))

/-- Points in the same equal-length cell differ by circle norm at most
`1 / m`. -/
theorem norm_sub_le_inv_of_circleCell_eq
    {m : Nat} (hm : 0 < m) {z w : AddCircle (1 : Real)}
    (hcell : circleCell m hm z = circleCell m hm w) :
    ‖z - w‖ ≤ 1 / (m : Real) := by
  let rz := circleRep z
  let rw := circleRep w
  let uz := (rz + 1 / 2) * (m : Real)
  let uw := (rw + 1 / 2) * (m : Real)
  have hrz : 0 ≤ rz + 1 / 2 := by
    dsimp [rz]
    linarith [(circleRep_mem z).1]
  have hrw : 0 ≤ rw + 1 / 2 := by
    dsimp [rw]
    linarith [(circleRep_mem w).1]
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have huz : 0 ≤ uz := by dsimp [uz]; positivity
  have huw : 0 ≤ uw := by dsimp [uw]; positivity
  have hfloor : ⌊uz⌋₊ = ⌊uw⌋₊ := by
    have hval := congrArg Fin.val hcell
    simpa only [circleCell, uz, uw, rz, rw] using hval
  have huzLower : ((⌊uz⌋₊ : Nat) : Real) ≤ uz := Nat.floor_le huz
  have huzUpper : uz < ((⌊uz⌋₊ : Nat) : Real) + 1 := Nat.lt_floor_add_one uz
  have huwLower : ((⌊uw⌋₊ : Nat) : Real) ≤ uw := Nat.floor_le huw
  have huwUpper : uw < ((⌊uw⌋₊ : Nat) : Real) + 1 := Nat.lt_floor_add_one uw
  have hdiffUpper : (rz - rw) * (m : Real) < 1 := by
    dsimp [uz, uw] at huzLower huzUpper huwLower huwUpper
    rw [hfloor] at huzLower huzUpper
    nlinarith
  have hdiffLower : -(1 / (m : Real)) < rz - rw := by
    have hmul : (-1 : Real) < (rz - rw) * (m : Real) := by
      dsimp [uz, uw] at huzLower huzUpper huwLower huwUpper
      rw [hfloor] at huzLower huzUpper
      nlinarith
    have hdiv : (-1 : Real) / (m : Real) < rz - rw :=
      (div_lt_iff₀ hmR).2 hmul
    simpa only [neg_div, one_div] using hdiv
  have hdiffUpper' : rz - rw < 1 / (m : Real) :=
    (lt_div_iff₀ hmR).2 hdiffUpper
  calc
    ‖z - w‖ ≤ |rz - rw| := norm_sub_le_abs_circleRep_sub z w
    _ ≤ 1 / (m : Real) := (abs_lt.2 ⟨hdiffLower, hdiffUpper'⟩).le

/-! ## The subset signature and its fibres -/

/-- Simultaneous `m`-cell signature on a finite complex-character basis. -/
def signature (Delta : Finset (AddChar G Complex))
    (m : Nat) (hm : 0 < m) (x : G) : Delta → Fin m :=
  fun psi ↦ circleCell m hm (circleLogCharacter psi.1 x)

/-- Membership in `adjoinBasis` is exactly old-dilate membership together
with all the newly adjoined width bounds. -/
theorem mem_adjoinBasis_carrier_iff
    (B : BohrData G) (Delta : Finset (AddChar G Complex))
    (kappa r : NNReal) (x : G) :
    x ∈ (adjoinBasis B Delta kappa r).carrier ↔
      x ∈ (B.dilate kappa).carrier ∧
        ∀ psi ∈ Delta, ‖circleLogCharacter psi x‖ ≤ (r : Real) := by
  classical
  constructor
  · intro hx
    refine ⟨adjoinBasis_carrier_subset_dilate B Delta kappa r hx, ?_⟩
    intro psi hpsi
    have hBasis := adjoinBasis_carrier_subset_basisBohrData B Delta kappa r hx
    exact (BohrData.mem_carrier _ _).mp hBasis (circleLogCharacter psi)
      (Finset.mem_image.mpr ⟨psi, hpsi, rfl⟩)
  · rintro ⟨hB, hDelta⟩
    rw [BohrData.mem_carrier] at hB ⊢
    intro gamma hgamma
    change gamma ∈ B.freq ∪ Delta.image circleLogCharacter at hgamma
    rw [Finset.mem_union] at hgamma
    change ‖gamma x‖ ≤
      (((if gamma ∈ B.freq then
          if gamma ∈ Delta.image circleLogCharacter then
            min (kappa * B.width gamma) r
          else kappa * B.width gamma
        else r) : NNReal) : Real)
    rcases hgamma with hOld | hNew
    · by_cases hNew' : gamma ∈ Delta.image circleLogCharacter
      · obtain ⟨psi, hpsi, hpsiGamma⟩ := Finset.mem_image.mp hNew'
        subst gamma
        rw [if_pos hOld, if_pos hNew']
        exact le_min (hB _ hOld) (hDelta psi hpsi)
      · rw [if_pos hOld, if_neg hNew']
        exact hB gamma hOld
    · obtain ⟨psi, hpsi, hpsiGamma⟩ := Finset.mem_image.mp hNew
      subst gamma
      by_cases hOld : circleLogCharacter psi ∈ B.freq
      · rw [if_pos hOld, if_pos hNew]
        exact le_min (hB _ hOld) (hDelta psi hpsi)
      · rw [if_neg hOld]
        exact hDelta psi hpsi

private theorem sub_mem_adjoinBasis_of_signature_eq
    (B : BohrData G) (Delta : Finset (AddChar G Complex))
    (kappa : NNReal) {m : Nat} (hm : 0 < m)
    (S : Finset G) (hS : S ⊆ (B.dilate kappa).carrier)
    {x y : ↥S} (hxy : signature Delta m hm x.1 = signature Delta m hm y.1) :
    x.1 - y.1 ∈
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier := by
  rw [mem_adjoinBasis_carrier_iff]
  constructor
  · exact BohrData.sub_mem_dilate (hS x.2) (hS y.2)
  · intro psi hpsi
    rw [map_sub]
    have hcoord := congrFun hxy ⟨psi, hpsi⟩
    have hbound := norm_sub_le_inv_of_circleCell_eq hm hcoord
    simpa only [NNReal.coe_inv, NNReal.coe_natCast, one_div] using hbound

private theorem card_signature_fiber_le
    (B : BohrData G) (Delta : Finset (AddChar G Complex))
    (kappa : NNReal) {m : Nat} (hm : 0 < m)
    (S : Finset G) (hS : S ⊆ (B.dilate kappa).carrier)
    (a : Delta → Fin m) :
    Fintype.card {x : ↥S // signature Delta m hm x.1 = a} ≤
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier.card := by
  classical
  by_cases hfiber : Nonempty {x : ↥S // signature Delta m hm x.1 = a}
  · let x₀ : {x : ↥S // signature Delta m hm x.1 = a} := Classical.choice hfiber
    let f : {x : ↥S // signature Delta m hm x.1 = a} →
        ↥(adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier :=
      fun x ↦ ⟨x.1.1 - x₀.1.1, sub_mem_adjoinBasis_of_signature_eq
        B Delta kappa hm S hS (x.2.trans x₀.2.symm)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card {x : ↥S // signature Delta m hm x.1 = a} ≤
          Fintype.card ↥(adjoinBasis B Delta (kappa + kappa)
            (m : NNReal)⁻¹).carrier := Fintype.card_le_of_injective f hf
      _ = (adjoinBasis B Delta (kappa + kappa)
            (m : NNReal)⁻¹).carrier.card := Fintype.card_coe _
  · simp only [not_nonempty_iff] at hfiber
    simp

/-! ## The relative-volume theorem -/

/-- **Subset-relative Bohr volume.**  Adjoining `Delta` at width `1/m` after
doubling the old scale costs at most `m ^ |Delta|`, measured relative to the
given subset `S` rather than relative to the ambient group. -/
theorem card_le_pow_mul_card_adjoinBasis
    (B : BohrData G) (Delta : Finset (AddChar G Complex))
    (kappa : NNReal) {m : Nat} (hm : 0 < m)
    (S : Finset G) (hS : S ⊆ (B.dilate kappa).carrier) :
    S.card ≤ m ^ Delta.card *
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier.card := by
  classical
  let Sigma := Delta → Fin m
  let q : ↥S → Sigma := fun x ↦ signature Delta m hm x.1
  have hfiber : ∀ a : Sigma,
      Fintype.card {x : ↥S // q x = a} ≤
        (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier.card := by
    intro a
    exact card_signature_fiber_le B Delta kappa hm S hS a
  have hcardSigma : Fintype.card Sigma = m ^ Delta.card := by
    dsimp [Sigma]
    rw [Fintype.card_pi]
    simp
  rw [← Fintype.card_coe S, ← hcardSigma]
  by_contra h
  have hlt : Fintype.card Sigma *
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier.card <
        Fintype.card ↥S := by omega
  obtain ⟨a, ha⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- The cardinality estimate together with the rank and subordination
properties of its explicit adjoined datum. -/
theorem controlled_adjoinBasis
    (B : BohrData G) (Delta : Finset (AddChar G Complex))
    (kappa : NNReal) {m : Nat} (hm : 0 < m)
    (S : Finset G) (hS : S ⊆ (B.dilate kappa).carrier) :
    (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).rank ≤
        B.rank + Delta.card ∧
      (adjoinBasis B Delta (kappa + kappa) (m : NNReal)⁻¹).carrier ⊆
        (B.dilate (kappa + kappa)).carrier ∧
      S.card ≤ m ^ Delta.card *
        (adjoinBasis B Delta (kappa + kappa)
          (m : NNReal)⁻¹).carrier.card := by
  exact ⟨adjoinBasis_rank_le B Delta _ _,
    adjoinBasis_carrier_subset_dilate B Delta _ _,
    card_le_pow_mul_card_adjoinBasis B Delta kappa hm S hS⟩

end

end RelativeBohrVolume

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/LocalizedAlmostPeriodicity.lean` -/

section
/-!
# The normalization step in localized almost-periodicity

The analytic Schoen--Sisask argument naturally controls the unnormalized
three-fold convolution `1_(-A₂) ⋆ 1_A₁ ⋆ 1_(-S)`.

The quantitative Roth iteration uses instead the probability-normalized
difference convolution `μ_A₁ ∘ μ_A₂` and convolution by a Bohr probability
measure.  This file proves the exact finite-sum change of variables between
the conventions and the final convexity step.  There is no implicit factor
of the order of the ambient group.
-/

open scoped BigOperators _root_.ENNReal Indicator _root_.NNReal Pointwise translate
open _root_.Finset _root_.Function _root_.MeasureTheory _root_.RCLike

namespace LocalizedAlmostPeriodicity

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-! ## Fourier control of a translation -/

/-- Chord distance from one is unchanged by negating the group argument. -/
lemma norm_character_neg_sub_one (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

/-! ## Fourier smoothing for a Croot--Sisask averaging measure -/

/-- Fourier inversion and the elementary large-spectrum split.  On Fourier
modes where the normalized indicator of `X` is at least `eta`, use the
supplied phase bound; on all remaining modes, the `m`-fold smoothing supplies
the factor `eta ^ m` and the universal chord bound two. -/
theorem smoothing_translate_dLinfty_le
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (X : Finset G) (hX : X.Nonempty) (m : ℕ) (F : G → ℂ)
    (eta theta : ℝ) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (t : G)
    (hphase : ∀ psi : AddChar G ℂ,
      eta ≤ ‖dft (μ_[ℂ] X) psi‖ → ‖1 - psi t‖ ≤ theta) :
    ‖τ t (μ X ∗ᵈ^ m ∗ᵈ F) - (μ X ∗ᵈ^ m ∗ᵈ F)‖_[∞] ≤
      (theta + 2 * eta ^ m) * ‖dft F‖ₙ_[1] := by
  rw [MeasureTheory.dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  let P : G → ℂ := μ X ∗ᵈ^ m ∗ᵈ F
  have hpoint :
      (τ t P - P) x =
        𝔼 psi : AddChar G ℂ,
          dft P psi * (psi (x - t) - psi x) := by
    simp only [Pi.sub_apply, translate_apply]
    rw [← dft_inversion P (x - t), ← dft_inversion P x,
      ← Finset.expect_sub_distrib]
    apply Finset.expect_congr rfl
    intro psi _
    ring
  rw [hpoint]
  calc
    ‖𝔼 psi : AddChar G ℂ,
        dft P psi * (psi (x - t) - psi x)‖
        ≤ 𝔼 psi : AddChar G ℂ,
            ‖dft P psi * (psi (x - t) - psi x)‖ :=
          RCLike.norm_expect_le (K := ℝ)
    _ ≤ 𝔼 psi : AddChar G ℂ,
          (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
      refine expect_le_expect fun psi _ ↦ ?_
      rw [norm_mul]
      have hfactor :
          ‖psi (x - t) - psi x‖ = ‖1 - psi t‖ := by
        have hmap : psi (x - t) = psi x * psi (-t) := by
          rw [sub_eq_add_neg, psi.map_add_eq_mul]
        rw [hmap]
        calc
          ‖psi x * psi (-t) - psi x‖ = ‖psi x * (psi (-t) - 1)‖ := by ring_nf
          _ = ‖psi (-t) - 1‖ := by rw [norm_mul, AddChar.norm_apply, one_mul]
          _ = ‖1 - psi t‖ := norm_character_neg_sub_one psi t
      rw [hfactor]
      simp only [P, dft_ddconv_apply, dft_iterConv_apply, norm_mul, norm_pow]
      have hmu : ‖dft (μ_[ℂ] X) psi‖ ≤ 1 := by
        calc
          ‖dft (μ_[ℂ] X) psi‖ ≤ ‖(μ_[ℂ] X)‖_[1] := norm_dft_le_dL1Norm _ _
          _ = 1 := MeasureTheory.dL1Norm_mu hX
      by_cases hlarge : eta ≤ ‖dft (μ_[ℂ] X) psi‖
      · have hpow : ‖dft (μ_[ℂ] X) psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi hlarge
        calc
          ‖dft (μ_[ℂ] X) psi‖ ^ m * ‖dft F psi‖ * ‖1 - psi t‖ ≤
              1 * ‖dft F psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hF : 0 ≤ ‖dft F psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖dft (μ_[ℂ] X) psi‖ ^ m ≤ eta ^ m := by
          exact pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖dft (μ_[ℂ] X) psi‖ ^ m * ‖dft F psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖dft F psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖dft F psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hF : 0 ≤ ‖dft F psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * ‖dft F‖ₙ_[1] := by
      rw [MeasureTheory.cL1Norm_eq_expect_norm, Finset.mul_expect]

/-- The Fourier `L¹` norm of the three-factor convolution appearing in the
Schoen--Sisask argument is bounded by the square root of the ratio of the last
two set sizes.  This is exactly Cauchy--Schwarz and Parseval; the first
probability factor has Fourier `L∞` norm at most one. -/
theorem dft_threefold_cL1Norm_le
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (A B C : Finset G) (hA : A.Nonempty) (hC : C.Nonempty) :
    ‖dft ((μ_[ℂ] A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ μ C)‖ₙ_[1] ≤
      Real.sqrt ((B.card : ℝ) / C.card) := by
  calc
    ‖dft ((μ_[ℂ] A ∗ᵈ (𝟭_[B] : G → ℂ)) ∗ᵈ μ C)‖ₙ_[1]
        = ‖dft (μ_[ℂ] A) *
            (dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C))‖ₙ_[1] := by
          rw [dft_ddconv, dft_ddconv]
          congr 1
          funext psi
          ring
    _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] := by
      calc
        _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] *
              ‖dft (μ_[ℂ] A)‖ₙ_[∞] := by
            simpa [mul_comm] using
              (cL1Norm_mul_le (f := dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C))
                (g := dft (μ_[ℂ] A)) 1 ∞)
        _ ≤ ‖dft (𝟭_[B] : G → ℂ) * dft (μ_[ℂ] C)‖ₙ_[1] * 1 := by
            gcongr
            exact (cLinftyNorm_dft_le_dL1Norm _).trans_eq (dL1Norm_mu hA)
        _ = _ := mul_one _
    _ ≤ ‖dft (𝟭_[B] : G → ℂ)‖ₙ_[2] * ‖dft (μ_[ℂ] C)‖ₙ_[2] :=
      cL1Norm_mul_le 2 2
    _ = Real.sqrt (B.card : ℝ) * (C.card : ℝ) ^ (-2⁻¹ : ℝ) := by
      rw [cL2Norm_dft, dL2Norm_indicator_one, cL2Norm_dft, dL2Norm_mu hC]
    _ = Real.sqrt ((B.card : ℝ) / C.card) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_eq_rpow,
        Real.sqrt_eq_rpow, div_eq_mul_inv]
      congr 1
      rw [← Real.rpow_neg (by positivity)]
      congr 1
      norm_num

/-- The unnormalized DFT of the uniform probability measure is the mass
Fourier coefficient at the negative character. -/
lemma dft_mu_eq_massCoeff_neg (X : Finset G) (psi : AddChar G ℂ) :
    dft (μ_[ℂ] X) psi =
      Erdos140.massCoeff (Erdos140.normalizedIndicator X) (-psi) := by
  classical
  rw [dft_apply, wInner_one_eq_sum]
  simp only [inner_apply', Erdos140.massCoeff, Pi.neg_apply,
    AddChar.neg_apply, AddChar.inv_apply_eq_conj]
  apply Finset.sum_congr rfl
  intro x _
  unfold mu Erdos140.normalizedIndicator
  by_cases hx : x ∈ X
  · simp [hx, smul_eq_mul, ← AddChar.inv_apply_eq_conj,
      ← AddChar.map_neg_eq_inv, mul_comm]
  · simp [hx, smul_eq_mul]

/-- Translation changes a discrete Fourier coefficient only by a unit
character phase, so its norm is unchanged. -/
lemma norm_dft_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    ‖dft (τ a f) psi‖ = ‖dft f psi‖ := by
  rw [dft_apply, dft_apply, wInner_one_eq_sum, wInner_one_eq_sum]
  simp only [inner_apply', translate_apply]
  have hsum :
      (∑ x : G, starRingEnd ℂ (psi x) * f (x - a)) =
        starRingEnd ℂ (psi a) * ∑ x : G, starRingEnd ℂ (psi x) * f x := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (-a)) _ _ (fun x ↦ ?_)
    simp only [Equiv.coe_addRight, sub_eq_add_neg, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, map_mul, map_inv₀]
    have hne : starRingEnd ℂ (psi a) ≠ 0 := by
      have hpsi : psi a ≠ 0 := by
        intro h
        have hnorm := AddChar.norm_apply psi a
        rw [h, norm_zero] at hnorm
        norm_num at hnorm
      simpa using hpsi
    field_simp
  rw [hsum, norm_mul]
  simp

/-- The Fourier norm of the uniform measure on a translated finite set is
unchanged. -/
lemma norm_dft_mu_vaddFinset (T : Finset G) (a : G) (psi : AddChar G ℂ) :
    ‖dft (μ_[ℂ] (a +ᵥ T)) psi‖ = ‖dft (μ_[ℂ] T) psi‖ := by
  rw [← translate_mu (K := ℂ)]
  exact norm_dft_translate (μ_[ℂ] T) a psi

/-- The half-large DFT spectrum of the probability measure agrees with the
half-large Chang spectrum used by the relative selector. -/
theorem mem_largeSpectrum_of_half_le_norm_dft_mu
    (X : Finset G) (hX : X.Nonempty) (psi : AddChar G ℂ)
    (hpsi : (1 / 2 : ℝ) ≤ ‖dft (μ_[ℂ] X) psi‖) :
    psi ∈ Erdos140.Chang.largeSpectrum X (1 / 2) := by
  classical
  by_contra hnot
  have hneg : -psi ∉ Erdos140.Chang.largeSpectrum X (1 / 2) := by
    intro hn
    have := Erdos140.RelativeChangSanders.neg_mem_chang_largeSpectrum hn
    exact hnot (by simpa only [neg_neg] using this)
  have hltSpec :
      ‖Erdos140.Chang.spectrumSum X (-psi)‖ < (1 / 2 : ℝ) * X.card := by
    exact lt_of_not_ge fun h ↦ hneg (Erdos140.Chang.mem_largeSpectrum.mpr h)
  have hcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hlt :
      ‖Erdos140.massCoeff (Erdos140.normalizedIndicator X) (-psi)‖ < 1 / 2 := by
    rw [Erdos140.massCoeff_normalizedIndicator, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcard]
    calc
      (X.card : ℝ)⁻¹ * ‖Erdos140.Chang.spectrumSum X (-psi)‖ <
          (X.card : ℝ)⁻¹ * ((1 / 2 : ℝ) * X.card) := by gcongr
      _ = 1 / 2 := by field_simp
  rw [dft_mu_eq_massCoeff_neg] at hpsi
  linarith

/-- A half-large Fourier mode of a translate of T is already in the
half-large Chang spectrum of T. -/
theorem mem_largeSpectrum_of_half_le_norm_dft_mu_vaddFinset
    (T : Finset G) (hT : T.Nonempty) (a : G) (psi : AddChar G ℂ)
    (hpsi : (1 / 2 : ℝ) ≤ ‖dft (μ_[ℂ] (a +ᵥ T)) psi‖) :
    psi ∈ Erdos140.Chang.largeSpectrum T (1 / 2) := by
  apply mem_largeSpectrum_of_half_le_norm_dft_mu T hT psi
  rw [← norm_dft_mu_vaddFinset T a psi]
  exact hpsi

/-- An explicit number of arc cells sufficient to annihilate a spectrum of
real-valued dimension at most `D`.  The `max` makes the definition total even
when it is used outside the positive-dimensional application. -/
noncomputable def spectralQuantization (D : ℝ) : ℕ :=
  ⌈2 * Real.pi * max D 0⌉₊ + 1

lemma spectralQuantization_pos (D : ℝ) : 0 < spectralQuantization D := by
  simp [spectralQuantization]

lemma mul_inv_spectralQuantization_le (D : ℝ) :
    D * ((((spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ)) ≤
      (2 * Real.pi)⁻¹ := by
  let n := spectralQuantization D
  have hnNat : 0 < n := spectralQuantization_pos D
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hceil : 2 * Real.pi * max D 0 ≤
      (Nat.ceil (2 * Real.pi * max D 0) : ℝ) := Nat.le_ceil _
  have hmain : 2 * Real.pi * D ≤ (n : ℝ) := by
    calc
      2 * Real.pi * D ≤ 2 * Real.pi * max D 0 := by
        gcongr
        exact le_max_left _ _
      _ ≤ (Nat.ceil (2 * Real.pi * max D 0) : ℝ) := hceil
      _ ≤ (n : ℝ) := by
        dsimp [n, spectralQuantization]
        exact_mod_cast Nat.le_succ _
  have hcoe : ((((n : ℕ) : ℝ≥0)⁻¹ : ℝ)) = (n : ℝ)⁻¹ := by
    norm_cast
  rw [hcoe]
  rw [← div_eq_mul_inv, div_le_iff₀ hn]
  calc
    D ≤ (n : ℝ) / (2 * Real.pi) :=
      (le_div_iff₀ hpi).2 (by nlinarith [hmain])
    _ = (2 * Real.pi)⁻¹ * (n : ℝ) := by
      field_simp

/-- Multiplying the number of spectral cells by a positive integer makes the
new-spectrum phase loss explicitly at most 2 / q.  This is the quantitative
form used by the density step: the dimension bound on Delta is the only
input beyond positivity of the scale multiplier. -/
lemma scaled_spectral_phase_le (D : ℝ) (d q : ℕ)
    (hd : (d : ℝ) ≤ D) (hq : 0 < q) :
    4 * Real.pi * (d : ℝ) *
        (((((q * spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ))) ≤
      2 / (q : ℝ) := by
  have hs : 0 < spectralQuantization D := spectralQuantization_pos D
  have hsR : (0 : ℝ) < spectralQuantization D := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase : D * ((spectralQuantization D : ℝ)⁻¹) ≤
      (2 * Real.pi)⁻¹ := by
    have h := mul_inv_spectralQuantization_le D
    have hcoe : ((((spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ)) =
        (spectralQuantization D : ℝ)⁻¹ := by norm_cast
    simpa [hcoe] using h
  have hdsmall : (d : ℝ) * ((spectralQuantization D : ℝ)⁻¹) ≤
      (2 * Real.pi)⁻¹ := by
    calc
      (d : ℝ) * ((spectralQuantization D : ℝ)⁻¹) ≤
          D * ((spectralQuantization D : ℝ)⁻¹) := by gcongr
      _ ≤ _ := hbase
  have hcoe : (((((q * spectralQuantization D : ℕ) : ℝ≥0)⁻¹ : ℝ))) =
      ((q : ℝ) * (spectralQuantization D : ℝ))⁻¹ := by
    norm_cast
  rw [hcoe, mul_inv]
  calc
    4 * Real.pi * (d : ℝ) *
        ((q : ℝ)⁻¹ * (spectralQuantization D : ℝ)⁻¹) =
        (q : ℝ)⁻¹ *
          (4 * Real.pi * ((d : ℝ) * (spectralQuantization D : ℝ)⁻¹)) := by ring
    _ ≤ (q : ℝ)⁻¹ * (4 * Real.pi * (2 * Real.pi)⁻¹) := by gcongr
    _ = 2 / (q : ℝ) := by
      field_simp
      ring

/-- Transfer almost-periodicity through a uniform smoothing approximation. -/
theorem transfer_smoothing_translate
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    (F P : G → ℂ) (t : G) {delta E : ℝ}
    (hdelta : ‖P - F‖_[∞] ≤ delta)
    (hperiod : ‖τ t P - P‖_[∞] ≤ E) :
    ‖τ t F - F‖_[∞] ≤ 2 * delta + E := by
  have hfirst :
      ‖τ t F - F‖_[∞] ≤ ‖τ t F - τ t P‖_[∞] + ‖τ t P - F‖_[∞] :=
    dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub le_top
  have hsecond :
      ‖τ t P - F‖_[∞] ≤ ‖τ t P - P‖_[∞] + ‖P - F‖_[∞] :=
    dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub le_top
  calc
    ‖τ t F - F‖_[∞] ≤ ‖τ t F - τ t P‖_[∞] + ‖τ t P - F‖_[∞] := hfirst
    _ ≤ ‖τ t F - τ t P‖_[∞] +
          (‖τ t P - P‖_[∞] + ‖P - F‖_[∞]) := by gcongr
    _ = ‖F - P‖_[∞] + (‖τ t P - P‖_[∞] + ‖P - F‖_[∞]) := by
      have htrans : τ t F - τ t P = τ t (F - P) := by rfl
      rw [htrans, dLpNorm_translate]
    _ ≤ delta + (E + delta) := by
      gcongr
      simpa [dLpNorm_sub_comm] using hdelta
    _ = 2 * delta + E := by ring

/-! ## Global Chang spectrum converted to a Bohr datum -/

/-- Relative Chang--Sanders geometry interface.  A local spectral selector
need only return the displayed signed-span-plus-old-spectrum cover; this
theorem supplies the adjoined datum, its relative volume, and its explicit
character-annihilation error. -/
theorem controlled_bohr_of_relativeSpectrum_cover
    (C : Erdos140.BohrData G) (hCreg : C.IsRankRegular)
    (Q Delta : Finset (AddChar G ℂ)) (kappa : ℝ≥0)
    (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (C.dilate kappa).carrier)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Erdos140.Chang.largeSpectrum C.carrier (1 / 2), psi = z + s) :
    let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
      (kappa + kappa) (m : ℝ≥0)⁻¹
    D.rank ≤ C.rank + Delta.card ∧
      D.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * D.carrier.card ∧
      ∀ t ∈ D.carrier, ∀ psi ∈ Q,
        ‖1 - psi t‖ ≤
          4 * Real.pi * ((Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ)) +
            400 * ((max C.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hcontrolled := Erdos140.RelativeBohrVolume.controlled_adjoinBasis
    C Delta kappa hm X hX
  refine ⟨hcontrolled.1, hcontrolled.2.1, hcontrolled.2.2, ?_⟩
  intro t ht psi hpsi
  simpa only [D, NNReal.coe_inv, NNReal.coe_natCast] using
    (Erdos140.LocalSpectrum.norm_one_sub_character_le_of_localSpectrum_cover
      C hCreg hsigma hsmall hcover t ht psi hpsi)

/-- Every finite Bohr datum has a rank-regular sub-dilate of the same rank.
Passing to it costs at most `4 ^ rank` in cardinality. -/
theorem exists_rankRegular_subdatum (D : Erdos140.BohrData G) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank = D.rank ∧ R.carrier ⊆ D.carrier ∧
        D.carrier.card ≤ 4 ^ D.rank * R.carrier.card := by
  classical
  obtain ⟨rho, hrhoHalf, hrhoOne, hreg⟩ := D.exists_rankRegular_dilate
  refine ⟨D.dilate rho, hreg, by simp, ?_, ?_⟩
  · simpa only [Erdos140.BohrData.dilate_one] using
      (Erdos140.BohrData.carrier_dilate_mono (B := D) hrhoOne)
  · have hbase := Erdos140.BohrData.card_unit_le_four_pow_rank_mul_card_half D
    have hhalf : (D.dilate (1 / 2)).carrier.card ≤
        (D.dilate rho).carrier.card :=
      Finset.card_le_card (Erdos140.BohrData.carrier_dilate_mono hrhoHalf)
    calc
      D.carrier.card = (D.dilate 1).carrier.card := by simp
      _ ≤ 4 ^ D.rank * (D.dilate (1 / 2)).carrier.card := hbase
      _ ≤ 4 ^ D.rank * (D.dilate rho).carrier.card :=
        Nat.mul_le_mul_left _ hhalf

/-- Rank-regular output for the relative Chang--Sanders cover interface. -/
theorem exists_regular_controlled_bohr_of_relativeSpectrum_cover
    (C : Erdos140.BohrData G) (hCreg : C.IsRankRegular)
    (Q Delta : Finset (AddChar G ℂ)) (kappa : ℝ≥0)
    (m : ℕ) (hm : 0 < m) (X : Finset G)
    (hX : X ⊆ (C.dilate kappa).carrier)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0))
    (hsmall : (Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ) ≤
      (2 * Real.pi)⁻¹)
    (hcover : ∀ psi ∈ Q, ∃ z ∈ Delta.addSpan,
      ∃ s ∈ Erdos140.Chang.largeSpectrum C.carrier (1 / 2), psi = z + s) :
    ∃ R : Erdos140.BohrData G,
      R.IsRankRegular ∧ R.rank ≤ C.rank + Delta.card ∧
      R.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
      X.card ≤ m ^ Delta.card * (4 ^ (C.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier, ∀ psi ∈ Q,
        ‖1 - psi t‖ ≤
          4 * Real.pi * ((Delta.card : ℝ) * ((m : ℝ≥0)⁻¹ : ℝ)) +
            400 * ((max C.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0) := by
  classical
  let D := Erdos140.LocalSpectrum.adjoinBasis C Delta
    (kappa + kappa) (m : ℝ≥0)⁻¹
  have hD := controlled_bohr_of_relativeSpectrum_cover
    C hCreg Q Delta kappa m hm X hX hsigma hsmall hcover
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ := exists_rankRegular_subdatum D
  refine ⟨R, hRreg, hRrank.le.trans hD.1, hRD.trans hD.2.1, ?_, ?_⟩
  · calc
      X.card ≤ m ^ Delta.card * D.carrier.card := hD.2.2.1
      _ ≤ m ^ Delta.card * (4 ^ D.rank * R.carrier.card) :=
        Nat.mul_le_mul_left _ hDcard
      _ ≤ m ^ Delta.card * (4 ^ (C.rank + Delta.card) * R.carrier.card) := by
        have hpow : 4 ^ D.rank ≤ 4 ^ (C.rank + Delta.card) :=
          Nat.pow_le_pow_right (by omega) hD.1
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
  · intro t ht psi hpsi
    exact hD.2.2.2 t (hRD ht) psi hpsi

/-- Unconditional local Chang--Sanders geometry, including regularization and
relative volume.  The logarithmic dimension parameter involves only the
density of `X` inside `B`; no ambient-group cardinality occurs.

The intermediate datum `C` is the explicit rank-regular small dilate selected
by `exists_relativeLargeSpectrum_cover`.  The final datum is subordinate to a
doubled dilate of `C`, has the advertised rank increment, annihilates the whole
`eta`-large spectrum of `X`, and has an explicit relative-cardinality loss. -/
theorem exists_regular_local_largeSpectrum_controlled_bohr
    (B : Erdos140.BohrData G) (hBreg : B.IsRankRegular)
    (X : Finset G) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) (kappa : ℝ≥0) (m : ℕ) (hm : 0 < m)
    (hsigma : kappa + kappa ≤
      1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsmall :
      Erdos140.RelativeChangSanders.localChangDimension B X eta *
          (((m : ℝ≥0)⁻¹ : ℝ)) ≤ (2 * Real.pi)⁻¹) :
    ∃ rho : ℝ≥0, ∃ C : Erdos140.BohrData G,
      ∃ Delta : Finset (AddChar G ℂ), ∃ R : Erdos140.BohrData G,
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.dilate (rho *
          Erdos140.RelativeChangSanders.localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤
          Erdos140.RelativeChangSanders.localChangDimension B X eta ∧
        Delta ⊆ Erdos140.Chang.largeSpectrum X eta ∧
        R.IsRankRegular ∧ R.rank ≤ B.rank + Delta.card ∧
        R.carrier ⊆ (C.dilate (kappa + kappa)).carrier ∧
        (C.dilate kappa).carrier.card ≤
          m ^ Delta.card * (4 ^ (B.rank + Delta.card) * R.carrier.card) ∧
        ∀ t ∈ R.carrier,
          ∀ psi ∈ Erdos140.Chang.largeSpectrum X eta,
            ‖1 - psi t‖ ≤
              4 * Real.pi *
                  (Delta.card : ℝ) * (((m : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) := by
  classical
  obtain ⟨rho, C, Delta, hrhoHalf, hrhoOne, hC, hCreg,
      hDeltaCard, hDeltaSpec, hcover⟩ :=
    Erdos140.RelativeChangSanders.exists_relativeLargeSpectrum_cover
      B hBreg X hX hXB eta heta
  have hCrank : C.rank = B.rank := by simp [hC]
  have hsigmaC : kappa + kappa ≤
      1 / (100 * (max C.rank 1 : ℕ) : ℝ≥0) := by
    simpa [hCrank] using hsigma
  have hinv : 0 ≤ (((m : ℝ≥0)⁻¹ : ℝ)) := by positivity
  have hsmallDelta :
      (Delta.card : ℝ) * (((m : ℝ≥0)⁻¹ : ℝ)) ≤
        (2 * Real.pi)⁻¹ :=
    (mul_le_mul_of_nonneg_right hDeltaCard hinv).trans hsmall
  obtain ⟨R, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_controlled_bohr_of_relativeSpectrum_cover
      C hCreg (Erdos140.Chang.largeSpectrum X eta) Delta kappa m hm
        (C.dilate kappa).carrier (fun _ hx ↦ hx) hsigmaC hsmallDelta hcover
  refine ⟨rho, C, Delta, R, hrhoHalf, hrhoOne, hC, hCreg,
    hDeltaCard, hDeltaSpec, hRreg, ?_, hRsub, ?_, ?_⟩
  · simpa [hCrank] using hRrank
  · simpa [hCrank] using hRcard
  · intro t ht psi hpsi
    simpa only [hCrank, mul_assoc] using hphase t ht psi hpsi

/-- Localized almost-periodicity with the relative Chang step applied to the
original Croot--Sisask set T inside the parent Bohr set.  The smoothing
measure still uses the recentered translate X, but translation invariance of
Fourier norms transfers every large mode of X back to T.  Consequently the
dimension and rank loss are controlled by the density of T in B₀. -/
theorem exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
    [MeasurableSpace G] [DiscreteMeasurableSpace G]
    {A : Finset G} (hA : A.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (m : ℕ) (hm : m ≠ 0)
    (M L : Finset G) (hM : M.Nonempty) (hL : L.Nonempty)
    (B₀ : Erdos140.BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : ℝ≥0)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : ℕ) : ℝ≥0))
    (qQuant : ℕ) (hqQuant : 0 < qQuant) :
    let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
    let sampleK := Erdos140.crootSisaskSampleSize q
      ((delta / m) / Real.exp 1)
    ∃ (T X : Finset G) (z : G) (rho : ℝ≥0),
      ∃ (C₀ : Erdos140.BohrData G)
        (Delta : Finset (AddChar G ℂ)) (R : Erdos140.BohrData G),
      T ⊆ B₀.carrier ∧ z ∈ T ∧ X = -z +ᵥ T ∧ X.Nonempty ∧
      (((A.card : ℝ) ^ sampleK / 2 * B₀.carrier.card) /
          ((A + B₀.carrier).card : ℝ) ^ sampleK ≤ T.card) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        Erdos140.RelativeChangSanders.localChangBaseScale B₀ T (1 / 2)) ∧
      C₀.IsRankRegular ∧
      (Delta.card : ℝ) ≤
        Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      Delta ⊆ Erdos140.Chang.largeSpectrum T (1 / 2) ∧
      R.IsRankRegular ∧ R.rank ≤ B₀.rank + Delta.card ∧
      R.carrier ⊆ (C₀.dilate (kappa + kappa)).carrier ∧
      (C₀.dilate kappa).carrier.card ≤
        (qQuant * spectralQuantization
              (Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
            Delta.card *
          (4 ^ (B₀.rank + Delta.card) * R.carrier.card) ∧
      ∀ t ∈ R.carrier,
        ‖τ t ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L) -
            ((μ_[ℂ] A ∗ᵈ (𝟭_[M] : G → ℂ)) ∗ᵈ μ L)‖_[∞] ≤
          2 * delta +
            (4 * Real.pi *
                  (Delta.card : ℝ) *
                    ((((qQuant * spectralQuantization
                      (Erdos140.RelativeChangSanders.localChangDimension
                        B₀ T (1 / 2)) : ℕ) : ℝ≥0)⁻¹ : ℝ)) +
                400 * ((max B₀.rank 1 : ℕ) : ℝ) *
                  (kappa + kappa : ℝ≥0) +
                2 * (1 / 2 : ℝ) ^ m) *
              Real.sqrt ((M.card : ℝ) / L.card) := by
  classical
  let q := ⌈1 + Real.log (min 1 ((L.card : ℝ) / M.card))⁻¹⌉₊
  let sampleK := Erdos140.crootSisaskSampleSize q
    ((delta / m) / Real.exp 1)
  obtain ⟨T, z, hTB₀, hzT, hXne, _hXdiff, hTcard, hsmooth⟩ :=
    Erdos140.croot_sisask_linfty_subset_boosted
      hA B₀.carrier_nonempty delta hdelta m hm M L hM hL
  let X : Finset G := -z +ᵥ T
  have hTne : T.Nonempty := ⟨z, hzT⟩
  let dim := Erdos140.RelativeChangSanders.localChangDimension B₀ T (1 / 2)
  let n := qQuant * spectralQuantization dim
  have hn : 0 < n := Nat.mul_pos hqQuant (spectralQuantization_pos dim)
  have hsmall : dim * (((n : ℝ≥0)⁻¹ : ℝ)) ≤ (2 * Real.pi)⁻¹ := by
    have hdim : 0 ≤ dim := by
      have hTcard : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
      have hcard : (T.card : ℝ) ≤ B₀.carrier.card := by
        exact_mod_cast Finset.card_le_card hTB₀
      have hratio : (1 : ℝ) ≤ 2 * (B₀.carrier.card : ℝ) / T.card := by
        rw [le_div_iff₀ hTcard]
        nlinarith
      have hlog : 0 ≤ Real.log (2 * (B₀.carrier.card : ℝ) / T.card) :=
        Real.log_nonneg hratio
      dsimp [dim, Erdos140.RelativeChangSanders.localChangDimension]
      positivity
    have hbase : dim *
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) ≤
          (2 * Real.pi)⁻¹ :=
      mul_inv_spectralQuantization_le dim
    have hbase_le_n : spectralQuantization dim ≤ n := by
      dsimp [n]
      exact Nat.le_mul_of_pos_left _ hqQuant
    have hinv : (((n : ℝ≥0)⁻¹ : ℝ)) ≤
        ((((spectralQuantization dim : ℕ) : ℝ≥0)⁻¹ : ℝ)) := by
      have hbase_pos : (0 : ℝ≥0) <
          (spectralQuantization dim : ℕ) := by
        exact_mod_cast spectralQuantization_pos dim
      have hn_pos : (0 : ℝ≥0) < n := by exact_mod_cast hn
      have hbase_le_n' : (spectralQuantization dim : ℝ≥0) ≤ n := by
        exact_mod_cast hbase_le_n
      exact_mod_cast (inv_le_inv₀ hn_pos hbase_pos).2 hbase_le_n'
    exact (mul_le_mul_of_nonneg_left hinv hdim).trans hbase
  obtain ⟨rho, C₀, Delta, R, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, hDeltaSpec, hRreg, hRrank, hRsub, hRcard, hphase⟩ :=
    exists_regular_local_largeSpectrum_controlled_bohr
      B₀ hB₀reg T hTne hTB₀ (1 / 2) (by norm_num)
        kappa n hn hkappa (by simpa [dim] using hsmall)
  let F : G → ℂ := (μ A ∗ᵈ 𝟭_[M]) ∗ᵈ μ L
  let P : G → ℂ := μ X ∗ᵈ^ m ∗ᵈ F
  let phase : ℝ :=
    4 * Real.pi * (Delta.card : ℝ) * (((n : ℝ≥0)⁻¹ : ℝ)) +
      400 * ((max B₀.rank 1 : ℕ) : ℝ) * (kappa + kappa : ℝ≥0)
  have hphase0 : 0 ≤ phase := by
    dsimp [phase]
    positivity
  have hFfourier : ‖dft F‖ₙ_[1] ≤ Real.sqrt ((M.card : ℝ) / L.card) := by
    simpa [F] using dft_threefold_cL1Norm_le A M L hA hL
  have hsmooth' : ‖P - F‖_[∞] ≤ delta := by
    simpa [P, F, X] using hsmooth
  have hperiod : ∀ t ∈ R.carrier,
      ‖τ t F - F‖_[∞] ≤
        2 * delta + (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
    intro t ht
    have hP := smoothing_translate_dLinfty_le X (by simpa [X] using hXne) m F
      (1 / 2) phase (by norm_num) hphase0 t (fun psi hpsi ↦
        hphase t ht psi
          (mem_largeSpectrum_of_half_le_norm_dft_mu_vaddFinset
            T hTne (-z) psi (by simpa [X] using hpsi)))
    have hP' : ‖τ t P - P‖_[∞] ≤
        (phase + 2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt ((M.card : ℝ) / L.card) := by
      calc
        ‖τ t P - P‖_[∞] ≤
            (phase + 2 * (1 / 2 : ℝ) ^ m) * ‖dft F‖ₙ_[1] := by
              simpa [P] using hP
        _ ≤ (phase + 2 * (1 / 2 : ℝ) ^ m) *
            Real.sqrt ((M.card : ℝ) / L.card) := by
              gcongr
    exact transfer_smoothing_translate F P t hsmooth' hP'
  refine ⟨T, X, z, rho, C₀, Delta, R, hTB₀, hzT, rfl,
    by simpa [X] using hXne, ?_, hrhoHalf, hrhoOne, ?_, hC₀reg,
    ?_, hDeltaSpec, hRreg, hRrank, hRsub, ?_, ?_⟩
  · simpa [q, sampleK] using hTcard
  · simpa using hC₀
  · simpa [dim] using hDeltaCard
  · simpa [n, dim] using hRcard
  · intro t ht
    simpa [F, phase, n, dim, mul_assoc] using hperiod t ht

/-- Probability-normalized indicator, equal to `1 / |A|` on `A`. -/
noncomputable def probabilityIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

/-- Unnormalized finite-sum convolution of two probability densities. -/
noncomputable def sumConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

/-- Difference convolution with counting measure. -/
noncomputable def differenceConvolution (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (y - x)

/-- Counting-measure inner product. -/
noncomputable def countingInner (f g : G → ℝ) : ℝ :=
  ∑ x : G, f x * g x

/-- The `{0,1}`-valued indicator of a finite set. -/
noncomputable def setIndicator (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then 1 else 0

@[simp] lemma setIndicator_apply_mem {A : Finset G} {x : G} (hx : x ∈ A) :
    setIndicator A x = 1 := by simp [setIndicator, hx]

@[simp] lemma setIndicator_apply_not_mem {A : Finset G} {x : G} (hx : x ∉ A) :
    setIndicator A x = 0 := by simp [setIndicator, hx]

/-- The unnormalized sum obtained by expanding
`1_(-A₂) ⋆ 1_A₁ ⋆ 1_(-S)` at `-t`. -/
noncomputable def tripleIndicatorSum
    (A₁ A₂ S : Finset G) (t : G) : ℝ :=
  ∑ a₁ : G, ∑ a₂ : G,
    setIndicator A₁ a₁ * setIndicator A₂ a₂ * setIndicator S (t + a₁ - a₂)

/-- Exact normalization bridge, with no ambient-cardinality factor.

The left side is `<(μ_A₁ ∘ μ_A₂)(·-t), 1_S>` in the convention
where each `μ_A` has total mass one. -/
theorem finiteInner_translate_differenceConvolution_eq
    {A₁ A₂ : Finset G} (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (S : Finset G) (t : G) :
    countingInner
        (fun x ↦ differenceConvolution (probabilityIndicator A₁)
          (probabilityIndicator A₂) (x - t))
        (setIndicator S) =
      tripleIndicatorSum A₁ A₂ S t / (A₁.card * A₂.card : ℝ) := by
  classical
  simp only [countingInner, differenceConvolution, probabilityIndicator,
    tripleIndicatorSum]
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  calc
    ∑ y : G, ∑ x : G,
        ((if y ∈ A₁ then (#A₁ : ℝ)⁻¹ else 0) *
          (if y - (x - t) ∈ A₂ then (#A₂ : ℝ)⁻¹ else 0)) * setIndicator S x
        = ((#A₁ : ℝ)⁻¹ * (#A₂ : ℝ)⁻¹) *
            ∑ y : G, ∑ x : G,
              setIndicator A₁ y * setIndicator A₂ (y - (x - t)) *
                setIndicator S x := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro x _
          simp only [setIndicator]
          split_ifs <;> ring
    _ = ((#A₁ : ℝ)⁻¹ * (#A₂ : ℝ)⁻¹) *
            ∑ a₁ : G, ∑ a₂ : G,
              setIndicator A₁ a₁ * setIndicator A₂ a₂ *
                setIndicator S (t + a₁ - a₂) := by
          congr 1
          apply sum_congr rfl
          intro a₁ _
          refine (Fintype.sum_equiv (Equiv.subLeft (t + a₁)) _ _ fun a₂ ↦ ?_).symm
          simp only [Equiv.subLeft_apply]
          congr 2 <;> abel
    _ = (∑ a₁ : G, ∑ a₂ : G,
            setIndicator A₁ a₁ * setIndicator A₂ a₂ *
              setIndicator S (t + a₁ - a₂)) /
          (A₁.card * A₂.card : ℝ) := by
          rw [div_eq_inv_mul]
          field_simp [hA₁.card_ne_zero, hA₂.card_ne_zero]

/-- Convolution by a nonempty normalized indicator is the uniform average of
translates. -/
lemma normalizedConvolution_normalizedIndicator_apply
    {D : Finset G} (hD : D.Nonempty) (f : G → ℝ) (x : G) :
    sumConvolution (probabilityIndicator D) f x =
      (∑ t ∈ D, f (x - t)) / D.card := by
  classical
  simp only [sumConvolution, probabilityIndicator]
  rw [← sum_subset (s₁ := D) (s₂ := univ)]
  · rw [div_eq_inv_mul, Finset.mul_sum]
    apply sum_congr rfl
    intro t ht
    rw [if_pos ht]
  · simp
  · intro t _ ht
    simp [ht]

/-- Averaging pointwise almost-periods over a nonempty set preserves the same
error. -/
theorem smoothing_inner_error_of_pointwise
    {D : Finset G} (hD : D.Nonempty)
    (f h : G → ℝ) {eps : ℝ}
    (hperiod : ∀ t ∈ D,
      |countingInner (fun x ↦ f (x - t)) h - countingInner f h| ≤ eps) :
    |countingInner (sumConvolution (probabilityIndicator D) f) h -
        countingInner f h| ≤ eps := by
  classical
  have hcard : (0 : ℝ) < D.card := by exact_mod_cast hD.card_pos
  have hsmooth :
      countingInner (sumConvolution (probabilityIndicator D) f) h =
        (∑ t ∈ D, countingInner (fun x ↦ f (x - t)) h) / D.card := by
    simp only [countingInner]
    simp_rw [normalizedConvolution_normalizedIndicator_apply hD]
    simp_rw [div_mul_eq_mul_div, sum_div, Finset.sum_mul]
    rw [sum_comm]
    simp_rw [← sum_div]
  rw [hsmooth]
  have hrewrite :
      (∑ t ∈ D, countingInner (fun x ↦ f (x - t)) h) / D.card - countingInner f h =
        (∑ t ∈ D,
          (countingInner (fun x ↦ f (x - t)) h - countingInner f h)) / D.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard.ne']
  rw [hrewrite, abs_div, abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  calc
    |∑ t ∈ D, (countingInner (fun x ↦ f (x - t)) h - countingInner f h)|
        ≤ ∑ t ∈ D,
            |countingInner (fun x ↦ f (x - t)) h - countingInner f h| :=
          abs_sum_le_sum_abs (fun t ↦
            countingInner (fun x ↦ f (x - t)) h - countingInner f h) D
    _ ≤ ∑ _t ∈ D, eps := sum_le_sum fun t ht ↦ hperiod t ht
    _ = eps * D.card := by simp [mul_comm]

/-- Localized normalized conclusion from an unnormalized `L∞`
almost-periodicity estimate for the triple sum. -/
theorem localized_inner_error_of_triple_almost_periods
    {D : BohrData G} {A₁ A₂ S : Finset G} {eps : ℝ}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (htriple : ∀ t ∈ D.carrier,
      |tripleIndicatorSum A₁ A₂ S t - tripleIndicatorSum A₁ A₂ S 0| ≤
        eps * (A₁.card : ℝ) * A₂.card) :
    |countingInner
          (sumConvolution (probabilityIndicator D.carrier)
            (differenceConvolution
              (probabilityIndicator A₁) (probabilityIndicator A₂)))
          (setIndicator S) -
        countingInner
          (differenceConvolution
            (probabilityIndicator A₁) (probabilityIndicator A₂))
          (setIndicator S)| ≤ eps := by
  classical
  apply smoothing_inner_error_of_pointwise D.carrier_nonempty
  intro t ht
  have hzero := finiteInner_translate_differenceConvolution_eq hA₁ hA₂ S (0 : G)
  simp only [sub_zero] at hzero
  rw [finiteInner_translate_differenceConvolution_eq hA₁ hA₂, hzero]
  rw [← sub_div, abs_div]
  have hcard : (0 : ℝ) < (A₁.card : ℝ) * A₂.card :=
    mul_pos (by exact_mod_cast hA₁.card_pos) (by exact_mod_cast hA₂.card_pos)
  rw [abs_of_pos hcard]
  apply (div_le_iff₀ hcard).2
  simpa [mul_assoc] using htriple t ht

end LocalizedAlmostPeriodicity

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/LocalizedUnbalancing.lean` -/

section
/-!
# Localized physical unbalancing on a regular Bohr set

This file is the normalization-sensitive bridge between physical unbalancing
and the balanced-restriction argument.  The weight is not assumed to have a
positive spectrum: it is explicitly the autocorrelation of the convolution
of two normalized Bohr indicators, and hence has the autocorrelation
representation required by `physical_pow_inner_nonneg`.

The width hypothesis is the concrete rank-scale bound

`kappa <= epsilon * |A| / (4800 * max(rank B,1) * |B|)`.

Thus it is `epsilon * alpha / (4800 * max(rank B,1))`, where `alpha` is the
relative density of `A` in `B`.  In particular, it has no dependence on the
cardinality of the ambient group.
-/

open _root_.Finset Fintype _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped BigOperators ComplexConjugate ComplexOrder _root_.ENNReal _root_.NNReal Pointwise

namespace LocalizedUnbalancing

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The smoothing function whose autocorrelation is the localized weight. -/
def smoothingBase (D E : Finset G) : G → ℝ≥0 :=
  μ_[ℝ≥0] D ∗ᵈ μ E

/-- The concrete spectrally-positive probability weight used in localized
unbalancing. -/
def smoothingWeight (D E : Finset G) : G → ℝ≥0 :=
  smoothingBase D E ○ᵈ smoothingBase D E

lemma smoothingBase_sum {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∑ x : G, smoothingBase D E x = 1 := by
  simp [smoothingBase, sum_ddconv, hD, hE]

lemma smoothingWeight_sum {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty) :
    ∑ x : G, smoothingWeight D E x = 1 := by
  simp [smoothingWeight, sum_dddconv, smoothingBase_sum hD hE]

lemma smoothingWeight_nonneg (D E : Finset G) :
    0 ≤ smoothingWeight D E := by
  simp [smoothingWeight]

/-- The complex autocorrelation representation of the concrete smoothing
weight. -/
lemma smoothingWeight_autocorrelation (D E : Finset G) :
    ((↑) ∘ smoothingBase D E : G → ℂ) ○ᵈ
        ((↑) ∘ smoothingBase D E) =
      (↑) ∘ smoothingWeight D E := by
  let b := smoothingBase D E
  calc
    ((↑) ∘ b : G → ℂ) ○ᵈ ((↑) ∘ b) =
        (↑) ∘ (((↑) ∘ b : G → ℝ) ○ᵈ ((↑) ∘ b)) := by
          exact (Complex.ofReal_comp_dddconv ((↑) ∘ b) ((↑) ∘ b)).symm
    _ = (↑) ∘ (b ○ᵈ b) := by
      rw [← NNReal.coe_comp_dddconv]
      rfl
    _ = (↑) ∘ smoothingWeight D E := by
      funext x
      rfl

/-- `BalancedRestriction.weightedLpNorm` agrees with APAP's weighted norm on
positive natural exponents. -/
lemma weightedLpNorm_eq_wLpNorm (w : G → ℝ≥0) (f : G → ℝ)
    {p : ℕ} (hp : 0 < p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p = ‖f‖_[p, w] := by
  rw [BalancedRestriction.weightedLpNorm_of_pos _ _ hp]
  rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp.ne') (by simp)]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    simp only [weightedAbsMoment, NNReal.smul_def, smul_eq_mul, norm_eq_abs,
      Function.comp_apply, ENNReal.toReal_natCast]
    rw [Real.rpow_natCast]
  · simp [one_div]

lemma weightedLpNorm_smul_of_nonneg
    (w : G → ℝ≥0) (f : G → ℝ) (c : ℝ) (hc : 0 ≤ c)
    {p : ℕ} (hp : 0 < p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) (c • f) p =
      c * BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p := by
  rw [weightedLpNorm_eq_wLpNorm w _ hp, weightedLpNorm_eq_wLpNorm w _ hp,
    wLpNorm_smul]
  simp [Real.norm_eq_abs, abs_of_nonneg hc]

lemma weightedLpNorm_le_add_of_add
    (w : G → ℝ≥0) (f g : G → ℝ) {p : ℕ} (hp : 1 ≤ p) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤
      BalancedRestriction.weightedLpNorm ((↑) ∘ w) (f + g) p +
        BalancedRestriction.weightedLpNorm ((↑) ∘ w) g p := by
  simp_rw [weightedLpNorm_eq_wLpNorm w _ (Nat.zero_lt_of_lt hp)]
  exact wLpNorm_le_add_wLpNorm_add (by exact_mod_cast hp) w f g

/-- A pointwise bound controls the local weighted norm for a probability
weight. -/
lemma weightedLpNorm_le_of_abs_le
    {w : G → ℝ≥0} (hw : ∑ x : G, w x = 1)
    {f : G → ℝ} {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : 0 < p)
    (hf : ∀ x, |f x| ≤ C) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤ C := by
  rw [weightedLpNorm_eq_wLpNorm w f hp]
  calc
    ‖f‖_[p, w] ≤ ‖(fun _ : G ↦ C)‖_[p, w] := by
      apply lpNorm_mono_real .of_discrete
      simpa [abs_of_nonneg hC] using hf
    _ = C := by
      rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp.ne') (by simp)]
      simp only [ENNReal.toReal_natCast]
      have hsum : ∑ x : G, (w x : ℝ) = 1 := by exact_mod_cast hw
      have heq : ∑ x : G, (w x : ℝ) * ‖C‖ ^ (p : ℝ) = C ^ p := by
        rw [norm_eq_abs, abs_of_nonneg hC, Real.rpow_natCast, ← Finset.sum_mul,
          hsum, one_mul]
      rw [show (∑ x : G, w x • ‖C‖ ^ (p : ℝ)) = C ^ p by
        simpa [NNReal.smul_def] using heq]
      exact Real.pow_rpow_inv_natCast hC hp.ne'

lemma weightedLpNorm_le_of_abs_le_on_support
    {w : G → ℝ≥0} (hw : ∑ x : G, w x = 1)
    {f : G → ℝ} {C : ℝ} (hC : 0 ≤ C) {p : ℕ} (hp : 0 < p)
    (hf : ∀ x, w x ≠ 0 → |f x| ≤ C) :
    BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p ≤ C := by
  let g : G → ℝ := fun x ↦ if w x = 0 then 0 else f x
  have hnorm : BalancedRestriction.weightedLpNorm ((↑) ∘ w) f p =
      BalancedRestriction.weightedLpNorm ((↑) ∘ w) g p := by
    rw [BalancedRestriction.weightedLpNorm_of_pos _ _ hp,
      BalancedRestriction.weightedLpNorm_of_pos _ _ hp]
    apply congrArg (fun z : ℝ ↦ z ^ (1 / (p : ℝ)))
    unfold weightedAbsMoment
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : w x = 0 <;> simp [g, hx]
  rw [hnorm]
  apply weightedLpNorm_le_of_abs_le hw hC hp
  intro x
  by_cases hx : w x = 0
  · simp [g, hx, hC]
  · simpa [g, hx] using hf x hx

/-- APAP's normalized measure agrees with the counting-probability indicator
used by the local Bohr files. -/
lemma mu_eq_normalizedIndicator (S : Finset G) :
    μ_[ℝ] S = normalizedIndicator S := by
  funext x
  by_cases hx : x ∈ S <;> simp [mu_apply, normalizedIndicator, hx]

/-- A mixed normalized correlation with a rank-regular Bohr measure is close
to the constant `1 / |B|` on a narrow dilate. -/
lemma abs_mixedCorrelation_sub_inv_card_le
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    |(μ_[ℝ] A ○ᵈ μ B.carrier) t - (B.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) := by
  have hB : B.carrier.Nonempty := B.carrier_nonempty
  have hbase :
      ∑ x : G, μ_[ℝ] A x * μ B.carrier x =
        (B.carrier.card : ℝ)⁻¹ := by
    calc
      ∑ x : G, μ_[ℝ] A x * μ B.carrier x =
          ∑ x : G, μ_[ℝ] A x * (B.carrier.card : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ A
        · rw [mu_apply, mu_apply]
          simp [hx, hAB hx]
        · simp [mu_apply, hx]
      _ = (B.carrier.card : ℝ)⁻¹ := by
        rw [← Finset.sum_mul, sum_mu ℝ hA, one_mul]
  have htranslate :
      ∑ x : G, |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| ≤
        200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ) := by
    simpa only [mu_eq_normalizedIndicator] using
      B.sum_abs_normalizedIndicator_translate_le_of_rankRegular hreg hkappa ht
  rw [dddconv_eq_sum_sub']
  simp only [starRingEnd_apply, star_trivial]
  rw [← hbase]
  rw [← Finset.sum_sub_distrib]
  have hrearrange :
      (∑ x : G, (μ_[ℝ] A x * μ B.carrier (x - t) -
        μ A x * μ B.carrier x)) =
      ∑ x : G, μ_[ℝ] A x *
        (μ B.carrier (x - t) - μ B.carrier x) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hrearrange]
  calc
    |∑ x : G, μ_[ℝ] A x *
        (μ B.carrier (x - t) - μ B.carrier x)| ≤
        ∑ x : G, |μ_[ℝ] A x *
          (μ B.carrier (x - t) - μ B.carrier x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x : G, μ_[ℝ] A x *
          |μ B.carrier (x - t) - μ B.carrier x| := by
      apply Finset.sum_congr rfl
      intro x _
      have hmuAx : 0 ≤ μ_[ℝ] A x := by
        rw [mu_apply]
        positivity
      rw [abs_mul, abs_of_nonneg hmuAx]
    _ ≤ ∑ x : G, (A.card : ℝ)⁻¹ *
          |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [mu_apply]
      split_ifs <;> simp
    _ = (A.card : ℝ)⁻¹ *
          ∑ x : G, |μ_[ℝ] B.carrier (x - t) - μ B.carrier x| := by
      rw [Finset.mul_sum]
    _ ≤ (A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) :=
      mul_le_mul_of_nonneg_left htranslate (by positivity)

/-- Expansion of the balanced autocorrelation, with every Bohr-boundary term
estimated explicitly. -/
lemma abs_positive_sub_baseline_add_balanced_le
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    {t : G} (ht : t ∈ (B.dilate kappa).carrier) :
    |(μ_[ℝ] A ○ᵈ μ A) t -
        ((B.carrier.card : ℝ)⁻¹ +
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier)) t)| ≤
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) := by
  let m : ℝ := (B.carrier.card : ℝ)⁻¹
  let eA : ℝ := (A.card : ℝ)⁻¹ *
    (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))
  let eB : ℝ := (B.carrier.card : ℝ)⁻¹ *
    (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))
  have hmix := abs_mixedCorrelation_sub_inv_card_le hreg hA hAB hkappa ht
  have hmixNeg := abs_mixedCorrelation_sub_inv_card_le hreg hA hAB hkappa
    (BohrData.neg_mem_carrier.mpr ht)
  have hreverse :
      |(μ_[ℝ] B.carrier ○ᵈ μ A) t - m| ≤ eA := by
    have hsym : (μ_[ℝ] B.carrier ○ᵈ μ A) t =
        (μ A ○ᵈ μ B.carrier) (-t) := by
      have h := dddconv_apply_neg (μ_[ℝ] A) (μ_[ℝ] B.carrier) t
      simpa using h.symm
    simpa [m, eA, hsym] using hmixNeg
  have hself := abs_mixedCorrelation_sub_inv_card_le hreg
    B.carrier_nonempty (fun _ h ↦ h) hkappa ht
  have hsum :
      |((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
        ((μ B.carrier ○ᵈ μ A) t - m) -
        ((μ B.carrier ○ᵈ μ B.carrier) t - m)| ≤
          2 * eA + eB := by
    calc
      |((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
          ((μ B.carrier ○ᵈ μ A) t - m) -
          ((μ B.carrier ○ᵈ μ B.carrier) t - m)| ≤
          |(μ_[ℝ] A ○ᵈ μ B.carrier) t - m| +
          |(μ B.carrier ○ᵈ μ A) t - m| +
          |(μ B.carrier ○ᵈ μ B.carrier) t - m| := by
            have hsub := abs_sub
              (((μ_[ℝ] A ○ᵈ μ B.carrier) t - m) +
                ((μ B.carrier ○ᵈ μ A) t - m))
              ((μ B.carrier ○ᵈ μ B.carrier) t - m)
            have hadd := abs_add_le
              ((μ_[ℝ] A ○ᵈ μ B.carrier) t - m)
              ((μ B.carrier ○ᵈ μ A) t - m)
            linarith
      _ ≤ eA + eA + eB := by gcongr
      _ = 2 * eA + eB := by ring
  have hexpand :
      (μ_[ℝ] A ○ᵈ μ A) t -
          (m + ((μ A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier)) t) =
        ((μ A ○ᵈ μ B.carrier) t - m) +
        ((μ B.carrier ○ᵈ μ A) t - m) -
        ((μ B.carrier ○ᵈ μ B.carrier) t - m) := by
    simp only [sub_dddconv, dddconv_sub, Pi.sub_apply]
    ring
  simpa [m, eA, eB, hexpand] using hsum

/-- Autocorrelation representation of the balanced autocorrelation after
normalizing its natural scale `1 / |B|` to one. -/
lemma scaled_balanced_autocorrelation
    (A K : Finset G) :
    ((Real.sqrt (K.card : ℝ) : ℂ) •
          ((↑) ∘ (μ_[ℝ] A - μ K) : G → ℂ)) ○ᵈ
        ((Real.sqrt (K.card : ℝ) : ℂ) •
          ((↑) ∘ (μ_[ℝ] A - μ K) : G → ℂ)) =
      (↑) ∘ ((K.card : ℝ) •
        ((μ_[ℝ] A - μ K) ○ᵈ (μ A - μ K))) := by
  rw [smul_dddconv, dddconv_smul]
  rw [← Complex.ofReal_comp_dddconv]
  funext x
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul,
    starRingEnd_apply]
  rw [show star (↑(Real.sqrt (K.card : ℝ)) : ℂ) =
      ↑(Real.sqrt (K.card : ℝ)) by simp]
  rw [← mul_assoc]
  norm_cast
  rw [← pow_two, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ K.card)]

/-- **Localized unbalancing on a rank-regular Bohr carrier.**

The smoothing weight is the explicit autocorrelation `smoothingWeight D E`;
there is no spectral-positivity assumption.  The geometric hypothesis
`hwidth` is exactly what follows from
`kappa ≤ epsilon * alpha / (4800 * max(rank B,1))` after writing
`alpha = |A| / |B|`. -/
theorem localized_unbalancing
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (B.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hlarge :
      epsilon * (B.carrier.card : ℝ)⁻¹ / 2 <
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ smoothingWeight D E)
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ
            (μ A - μ B.carrier))
          (BalancedRestriction.comparisonExponent p)) :
    ∃ r : ℕ, 0 < r ∧ Even r ∧
      r ≤ BalancedRestriction.stoppingExponent epsilon p ∧
      (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ smoothingWeight D E) (μ_[ℝ] A ○ᵈ μ A) r := by
  let K := B.carrier
  let nu := smoothingWeight D E
  let balanced : G → ℝ := μ_[ℝ] A - μ K
  let corr : G → ℝ := balanced ○ᵈ balanced
  let positive : G → ℝ := μ_[ℝ] A ○ᵈ μ A
  let main : ℝ := (K.card : ℝ)⁻¹
  let f : G → ℝ := (K.card : ℝ) • corr
  let surrogate : G → ℝ := main • (f + 1)
  have hK : K.Nonempty := B.carrier_nonempty
  have hKcard : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hmain : 0 < main := by simp [main, hKcard]
  have hmass : ∑ x : G, nu x = 1 := smoothingWeight_sum hD hE
  have hprob : BalancedRestriction.ProbabilityWeight ((↑) ∘ nu) :=
    ⟨fun x ↦ by exact_mod_cast (show 0 ≤ nu x by exact smoothingWeight_nonneg D E x),
      by simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hmass⟩
  have hfrep :
      ((Real.sqrt (K.card : ℝ) : ℂ) • ((↑) ∘ balanced : G → ℂ)) ○ᵈ
          ((Real.sqrt (K.card : ℝ) : ℂ) • ((↑) ∘ balanced : G → ℂ)) =
        (↑) ∘ f := by
    simpa [K, balanced, corr, f] using scaled_balanced_autocorrelation A K
  have hnurep :
      ((↑) ∘ smoothingBase D E : G → ℂ) ○ᵈ
          ((↑) ∘ smoothingBase D E) = (↑) ∘ nu := by
    simpa [nu] using smoothingWeight_autocorrelation D E
  have hmom : ∀ k : ℕ, 0 ≤ weightedMoment ((↑) ∘ nu) f k := by
    intro k
    have h := physical_pow_inner_nonneg hfrep hnurep k
    simpa [weightedMoment, wInner_one_eq_sum, RCLike.inner_apply, mul_comm] using h
  have hcardmain : (K.card : ℝ) * main = 1 := by
    simp [main, ne_of_gt hKcard]
  have hlargeF : epsilon / 2 <
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f
        (BalancedRestriction.comparisonExponent p) := by
    rw [show f = (K.card : ℝ) • corr by rfl,
      weightedLpNorm_smul_of_nonneg nu corr (K.card : ℝ) (by positivity)
        (by simp [BalancedRestriction.comparisonExponent, hp])]
    have hlarge' : epsilon * main / 2 <
        BalancedRestriction.weightedLpNorm ((↑) ∘ nu) corr
          (BalancedRestriction.comparisonExponent p) := by
      simpa [K, nu, balanced, corr, main] using hlarge
    nlinarith
  let qOdd := BalancedRestriction.unbalancingInputExponent p
  have hqOdd : 0 < qOdd := by
    have := BalancedRestriction.five_le_unbalancingInputExponent hp
    omega
  have hpromote := BalancedRestriction.weightedLpNorm_comparison_le_unbalancingInput
    hprob hp (f := f)
  have hlargeOdd : epsilon / 2 <
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f qOdd := by
    exact hlargeF.trans_le (by simpa [qOdd] using hpromote)
  have hmomentLarge : (epsilon / 2) ^ qOdd ≤
      weightedAbsMoment ((↑) ∘ nu) f qOdd := by
    calc
      (epsilon / 2) ^ qOdd ≤
          BalancedRestriction.weightedLpNorm ((↑) ∘ nu) f qOdd ^ qOdd :=
        pow_le_pow_left₀ (by positivity) hlargeOdd.le qOdd
      _ = weightedAbsMoment ((↑) ∘ nu) f qOdd :=
        BalancedRestriction.weightedLpNorm_pow hprob hqOdd
  have hscale : ∀ x, surrogate x = main * (1 + f x) := by
    intro x
    simp [surrogate, smul_eq_mul, add_comm]
    ring
  obtain ⟨r, hr, hreven, hrBound, hsurrogate⟩ :=
    BalancedRestriction.unbalancing_of_exact_scaling hprob
      (f := f) (positiveCorr := surrogate) (η := epsilon / 2)
      (mainTerm := main) (by positivity) (by linarith) hmain
      (BalancedRestriction.five_le_unbalancingInputExponent hp)
      (BalancedRestriction.unbalancingInputExponent_odd p) hmom hmomentLarge hscale
  have hrStop : r ≤ BalancedRestriction.stoppingExponent epsilon p := by
    simpa [BalancedRestriction.stoppingExponent, qOdd] using hrBound
  have herrorPoint : ∀ x, nu x ≠ 0 → |positive x - surrogate x| ≤ epsilon / 8 * main := by
    intro x hx
    have hb := abs_positive_sub_baseline_add_balanced_le hreg hA hAB hkappa
      (hsupport x hx)
    have hsurrogatePoint : surrogate x = main + corr x := by
      simp [surrogate, f, smul_eq_mul]
      rw [← mul_assoc, show main * (K.card : ℝ) = 1 by nlinarith, one_mul]
      ring
    simpa [K, balanced, corr, positive, main, hsurrogatePoint] using hb.trans hwidth
  have herror :
      BalancedRestriction.weightedLpNorm ((↑) ∘ nu) (positive - surrogate) r ≤
        epsilon / 8 * main := by
    apply weightedLpNorm_le_of_abs_le_on_support hmass
      (mul_nonneg (by positivity) hmain.le) hr
    intro x hx
    simpa [Pi.sub_apply] using herrorPoint x hx
  have htriangle := weightedLpNorm_le_add_of_add nu surrogate (positive - surrogate)
    (Nat.succ_le_iff.mpr hr)
  have hadd : surrogate + (positive - surrogate) = positive := by ext x; simp
  rw [hadd] at htriangle
  refine ⟨r, hr, hreven, hrStop, ?_⟩
  simpa [K, nu, positive, main] using (by nlinarith [hsurrogate, htriangle, herror])

end

end LocalizedUnbalancing

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/DensityStep.lean` -/

section
/-!
# The concrete regular-Bohr density step

This file contains the set-theoretic part of the Kelley--Meka/Bloom--Sisask
count-or-increment step.  There are two normalization points which are easy
to lose in an informal argument.

* Intersecting two Bohr data means taking the old width on an old-only
  frequency, the new width on a new-only frequency, and the minimum on a
  shared frequency.
* If `x - c` is in the old restricted set, the new *centred* restricted set
  contains `-c`, not `c`.  With this convention its new location is
  `oldShift - x`, and membership in the original set is preserved exactly.

The final narrowing theorem below takes actual regular child carriers and
returns either the simultaneous dense-translate alternative used by the
analytic count argument, or an actual `BohrStopping.RegularRestriction` with
the advertised density increment.  No numerical state is manufactured.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal translate

namespace DensityStep

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Intersections and frequency extensions -/

namespace Refinement

/-- The intersection of two finite Bohr data.  Frequencies occurring in both
data receive the smaller width. -/
def meet (B C : BohrData G) : BohrData G where
  freq := B.freq ∪ C.freq
  width gamma :=
    if gamma ∈ B.freq then
      if gamma ∈ C.freq then min (B.width gamma) (C.width gamma)
      else B.width gamma
    else C.width gamma

@[simp] theorem freq_meet (B C : BohrData G) :
    (meet B C).freq = B.freq ∪ C.freq := rfl

@[simp] theorem mem_meet_carrier (B C : BohrData G) (x : G) :
    x ∈ (meet B C).carrier ↔ x ∈ B.carrier ∧ x ∈ C.carrier := by
  classical
  simp only [BohrData.mem_carrier, meet, mem_union]
  constructor
  · intro hx
    constructor
    · intro gamma hgamma
      have h := hx gamma (Or.inl hgamma)
      by_cases hC : gamma ∈ C.freq
      · have h' : ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := by
          simpa [meet, hgamma, hC] using h
        calc
          ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := h'
          _ ≤ (B.width gamma : NNReal) := by exact_mod_cast min_le_left _ _
      · simpa [hgamma, hC] using h
    · intro gamma hgamma
      have h := hx gamma (Or.inr hgamma)
      by_cases hB : gamma ∈ B.freq
      · have h' : ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := by
          simpa [meet, hB, hgamma] using h
        calc
          ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := h'
          _ ≤ (C.width gamma : NNReal) := by exact_mod_cast min_le_right _ _
      · simpa [hB] using h
  · rintro ⟨hB, hC⟩ gamma (hgammaB | hgammaC)
    · by_cases hgammaC' : gamma ∈ C.freq
      · simpa [hgammaB, hgammaC'] using
          (le_min (hB gamma hgammaB) (hC gamma hgammaC'))
      · simpa [hgammaB, hgammaC'] using hB gamma hgammaB
    · by_cases hgammaB : gamma ∈ B.freq
      · simpa [hgammaB, hgammaC] using
          (le_min (hB gamma hgammaB) (hC gamma hgammaC))
      · simpa [hgammaB] using hC gamma hgammaC

/-- Bohr data with a prescribed common width on a finite frequency set. -/
def onFrequencies (Delta : Finset (AddCharacter G)) (width : NNReal) : BohrData G where
  freq := Delta
  width := fun _ => width

@[simp] theorem rank_onFrequencies (Delta : Finset (AddCharacter G)) (width : NNReal) :
    (onFrequencies Delta width).rank = Delta.card := rfl

@[simp] theorem mem_onFrequencies_carrier
    (Delta : Finset (AddCharacter G)) (width : NNReal) (x : G) :
    x ∈ (onFrequencies Delta width).carrier ↔
      ∀ gamma ∈ Delta, ‖gamma x‖ ≤ (width : Real) := by
  simp [onFrequencies, BohrData.mem_carrier]

/-- Add a finite family of common-width frequencies to an existing datum. -/
def extend (B : BohrData G) (Delta : Finset (AddCharacter G)) (width : NNReal) :
    BohrData G :=
  meet B (onFrequencies Delta width)

@[simp] theorem mem_extend_carrier (B : BohrData G)
    (Delta : Finset (AddCharacter G)) (width : NNReal) (x : G) :
    x ∈ (extend B Delta width).carrier ↔
      x ∈ B.carrier ∧ ∀ gamma ∈ Delta, ‖gamma x‖ ≤ (width : Real) := by
  rw [extend, mem_meet_carrier, mem_onFrequencies_carrier]

end Refinement

/-! ## Located regular restrictions -/

open BohrStopping

/-- A regular restriction together with an exact translation back into the
fixed original set.  This is the provenance needed to lift a local mixed
progression count to the original progression count. -/
structure LocatedRestriction (original : Finset G) where
  restriction : RegularRestriction G
  shift : G
  subset_original :
    ∀ x ∈ restriction.set, x - shift ∈ original

namespace LocatedRestriction

def ambient {original : Finset G} (s : LocatedRestriction original) : Finset G :=
  s.restriction.ambient

def density {original : Finset G} (s : LocatedRestriction original) : Real :=
  s.restriction.density

def rank {original : Finset G} (s : LocatedRestriction original) : Nat :=
  s.restriction.rank

def card {original : Finset G} (s : LocatedRestriction original) : Nat :=
  s.restriction.card

lemma density_pos {original : Finset G} (s : LocatedRestriction original) :
    0 < s.density := s.restriction.density_pos

lemma density_le_one {original : Finset G} (s : LocatedRestriction original) :
    s.density ≤ 1 := s.restriction.density_le_one

end LocatedRestriction

/-- A chain of controlled increments which retains a translation into the
same original set at every node. -/
inductive LocatedControlledChain {original : Finset G}
    (q : Real) (rankCost : Nat) (sizeCost : Real) :
    Nat → LocatedRestriction original → LocatedRestriction original → Prop
  | nil (s : LocatedRestriction original) :
      LocatedControlledChain q rankCost sizeCost 0 s s
  | cons {n : Nat} {s t u : LocatedRestriction original}
      (hst : IsControlledIncrement q rankCost sizeCost
        s.restriction t.restriction)
      (htu : LocatedControlledChain q rankCost sizeCost n t u) :
      LocatedControlledChain q rankCost sizeCost (n + 1) s u

namespace LocatedControlledChain

theorem forget {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    ControlledChain q rankCost sizeCost n s.restriction t.restriction := by
  induction h with
  | nil s => exact ControlledChain.nil s.restriction
  | cons hst _ ih => exact ControlledChain.cons hst ih

theorem density_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} (hq : 0 ≤ q) {n : Nat}
    {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    q ^ n * s.density ≤ t.density :=
  h.forget.density_bound hq

theorem rank_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    t.rank ≤ s.rank + n * rankCost :=
  h.forget.rank_bound

theorem card_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    Real.exp (-(n : Real) * sizeCost) * (s.card : Real) ≤ (t.card : Real) :=
  h.forget.card_bound

end LocatedControlledChain

/-! ## The centred translated fiber -/

/-- Negated fibre of the translate `x - C` inside `A`.  Negation recentres
the fibre inside the symmetric Bohr carrier containing `C`. -/
def narrowingSet (A C : Finset G) (x : G) : Finset G :=
  (C.filter fun c => x - c ∈ A).image fun c => -c

@[simp] theorem mem_narrowingSet {A C : Finset G} {x z : G} :
    z ∈ narrowingSet A C x ↔ -z ∈ C ∧ x + z ∈ A := by
  classical
  simp only [narrowingSet, mem_image, mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, hxc⟩, rfl⟩
    exact ⟨by simpa, by simpa [sub_eq_add_neg] using hxc⟩
  · rintro ⟨hzC, hxzA⟩
    refine ⟨-z, ?_, by simp⟩
    exact ⟨hzC, by simpa [sub_eq_add_neg] using hxzA⟩

theorem card_narrowingSet (A C : Finset G) (x : G) :
    (narrowingSet A C x).card = (C.filter fun c => x - c ∈ A).card := by
  classical
  unfold narrowingSet
  rw [Finset.card_image_of_injective]
  intro a b h
  exact neg_injective h

theorem narrowingSet_subset_carrier
    {B : BohrData G} {rho : NNReal} {A C : Finset G} {x : G}
    (hC : C ⊆ (B.dilate rho).carrier) :
    narrowingSet A C x ⊆ (B.dilate rho).carrier := by
  intro z hz
  have hz' := (mem_narrowingSet.mp hz).1
  exact BohrData.neg_mem_carrier.mp (hC hz')

/-- Exact normalization of a local density as the cardinality of the centred
translated fibre. -/
theorem localDensity_eq_card_narrowingSet_div
    {A C : Finset G} (hC : C.Nonempty) (x : G) :
    localDensity A C x = (narrowingSet A C x).card / (C.card : Real) := by
  classical
  rw [localDensity, normalizedConvolution]
  let e : G ≃ G := Equiv.subLeft x
  rw [Fintype.sum_equiv e
    (fun y : G => finsetIndicator A y * normalizedIndicator C (x - y))
    (fun c : G => finsetIndicator A (x - c) * normalizedIndicator C c)
    (fun c => by simp [e])]
  rw [card_narrowingSet]
  simp only [finsetIndicator, normalizedIndicator, div_eq_mul_inv]
  have hpoint (c : G) :
      (if x - c ∈ A then (1 : Real) else 0) *
          (if c ∈ C then (C.card : Real)⁻¹ else 0) =
        if c ∈ C ∧ x - c ∈ A then (C.card : Real)⁻¹ else 0 := by
    by_cases hc : c ∈ C <;> by_cases ha : x - c ∈ A <;> simp [hc, ha]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun c : G => c ∈ C ∧ x - c ∈ A) =
        C.filter fun c => x - c ∈ A := by
    ext c
    simp
  rw [hfilter]
  simp

/-! ## Sifting and localized-almost-periodicity normalization -/

open _root_.Function _root_.MeasureTheory _root_.Real
open scoped _root_.ENNReal Indicator Pointwise

/-- APAP's probability indicator is the same counting-probability indicator
used by the local almost-periodicity file. -/
theorem probabilityIndicator_eq_mu (A : Finset G) :
    LocalizedAlmostPeriodicity.probabilityIndicator A = μ_[Real] A := by
  funext x
  simp [LocalizedAlmostPeriodicity.probabilityIndicator, mu_apply]

/-- APAP's discrete difference convolution and the explicit one-variable
counting sum in `LocalizedAlmostPeriodicity` agree exactly. -/
theorem differenceConvolution_probability_eq_dddconv (A₁ A₂ : Finset G) :
    LocalizedAlmostPeriodicity.differenceConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
        (LocalizedAlmostPeriodicity.probabilityIndicator A₂) =
      μ_[Real] A₁ ○ᵈ μ A₂ := by
  funext x
  rw [probabilityIndicator_eq_mu, probabilityIndicator_eq_mu,
    LocalizedAlmostPeriodicity.differenceConvolution, dddconv_eq_sum_sub']
  simp

/-- The complex threefold convolution used by Croot--Sisask is the complex
embedding of the real counting inner product used by the localized triple
sum.  This is the sign-sensitive normalization bridge: the first set is
negated, while the sampling set is the unnormalised middle indicator. -/
theorem threefold_eq_ofReal_finiteInner
    (A₁ A₂ S : Finset G) (t : G) :
    ((μ_[ℂ] (-A₁) ∗ᵈ (𝟭_[S] : G → ℂ)) ∗ᵈ μ A₂) t =
      Complex.ofReal
        (LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S)) := by
  classical
  let a : G → Real := μ_[Real] A₁
  let b : G → Real := μ_[Real] A₂
  let oneS : G → Real := 𝟭_[S]
  have hcount :
      LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S) =
        ⟪τ t (a ○ᵈ b), oneS⟫_[Real] := by
    rw [differenceConvolution_probability_eq_dddconv]
    unfold LocalizedAlmostPeriodicity.countingInner
      LocalizedAlmostPeriodicity.setIndicator
    simp only [RCLike.wInner_one_eq_sum, RCLike.inner_apply',
      RCLike.conj_to_real, translate_apply, a, b, oneS, Set.indicator_apply,
      mem_coe]
  have hreal :
      ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b) t =
        LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    calc
      ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b) t =
          ((oneS ∗ᵈ b) ∗ᵈ μ_[Real] (-A₁)) t := by
            apply congrFun
            calc
              (μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b =
                  oneS ∗ᵈ (μ_[Real] (-A₁) ∗ᵈ b) := by
                    rw [ddconv_comm (μ_[Real] (-A₁)) oneS,
                      ddconv_assoc]
              _ = oneS ∗ᵈ (b ∗ᵈ μ_[Real] (-A₁)) := by
                    rw [ddconv_comm (μ_[Real] (-A₁)) b]
              _ = (oneS ∗ᵈ b) ∗ᵈ μ_[Real] (-A₁) := by
                    rw [ddconv_assoc]
      _ = ((oneS ∗ᵈ b) ○ᵈ a) t := by
        rw [← conjneg_mu (K := Real) A₁, ddconv_conjneg]
      _ = ⟪τ t a, oneS ∗ᵈ b⟫_[Real] := by
        rw [dddconv_eq_wInner_one]
        exact RCLike.conj_wInner_symm (𝕜 := Real)
          (1 : G → Real) (oneS ∗ᵈ b) (τ t a)
      _ = ⟪τ t a ○ᵈ b, oneS⟫_[Real] := by
        exact (dddconv_wInner_one_eq_wInner_one_ddconv
          (τ t a) b oneS).symm
      _ = ⟪τ t (a ○ᵈ b), oneS⟫_[Real] := by rw [translate_dddconv]
      _ = _ := hcount.symm
  have honeS : ((↑) ∘ oneS : G → Complex) = (𝟭_[S] : G → Complex) := by
    ext x
    by_cases hx : x ∈ S <;> simp [oneS, Set.indicator_apply, hx]
  rw [← hreal]
  change ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂) t =
    (Complex.ofReal ∘ ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b)) t
  rw [Complex.ofReal_comp_ddconv, Complex.ofReal_comp_ddconv]
  simp only [Complex.ofReal_comp_mu, b]
  rw [honeS]

/-- Pairing a probability difference convolution with a set indicator is
the literal mass of that convolution on the set. -/
theorem countingInner_difference_setIndicator_eq_sum
    (A₁ A₂ S : Finset G) :
    LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
        (LocalizedAlmostPeriodicity.setIndicator S) =
      ∑ x ∈ S, (μ_[Real] A₁ ○ᵈ μ A₂) x := by
  classical
  rw [differenceConvolution_probability_eq_dddconv]
  unfold LocalizedAlmostPeriodicity.countingInner
    LocalizedAlmostPeriodicity.setIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun x : G => x ∈ S) = S := by ext; simp
  rw [hfilter]

/-- The exact convexity consequence of the localized almost-periodicity
bridge: a popular-difference mass `1-delta` remains at least
`1-delta-epsilon` after smoothing by the actual Bohr probability measure. -/
theorem smoothed_popular_mass_lower_bound
    {D : BohrData G} {A₁ A₂ S : Finset G} {epsilon delta : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hmass : 1 - delta ≤ ∑ x ∈ S, (μ_[Real] A₁ ○ᵈ μ A₂) x)
    (htriple : ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        epsilon * (A₁.card : Real) * A₂.card) :
    1 - delta - epsilon ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D.carrier)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S) := by
  have herr :=
    LocalizedAlmostPeriodicity.localized_inner_error_of_triple_almost_periods
      hA₁ hA₂ htriple
  have hbase :
      1 - delta ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    rwa [countingInner_difference_setIndicator_eq_sum]
  have hlower := (abs_le.mp herr).1
  linarith

section SiftingOutput

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The exact common density lower bound delivered by the sifting lemma.
Keeping this expression named prevents the two copies in the output
certificate from silently acquiring different normalizations. -/
def siftingDensityLower (A B₁ B₂ : Finset G) (p : Nat) : Real :=
  (4 : Real)⁻¹ *
      ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
    (A.card : Real) ^ (2 * p)

/-- The explicit shift count used by the elementary sifting identity is
exactly the unnormalised indicator autocorrelation. -/
theorem commonShiftCount_eq_indicatorCorrelation
    (A : Finset G) (x : G) :
    (Sifting.commonShiftCount A x : Real) =
      (𝟭_[A, Real] ○ᵈ 𝟭_[A]) x := by
  classical
  rw [Sifting.commonShiftCount, dddconv_eq_sum_sub']
  have hcount :
      ((#(Finset.univ.filter fun t : G ↦ x - t ∈ A ∧ -t ∈ A) : Nat) : Real) =
        ∑ t : G, if x - t ∈ A ∧ -t ∈ A then (1 : Real) else 0 := by
    simpa using congrArg (fun n : Nat ↦ (n : Real))
      (Finset.card_filter (fun t : G ↦ x - t ∈ A ∧ -t ∈ A) Finset.univ)
  rw [hcount]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y ↦ ?_)
  simp only [Equiv.subLeft_apply, Set.indicator_apply]
  have hneg : x - y - x = -y := by abel
  rw [hneg]
  split_ifs <;> simp_all

/-- The common-tuple sifted sets have the exact product-cardinality moment
which drives the high-product selection in dependent random choice.  This
version is public and, unlike the existential DRC wrapper, retains the tuple
which witnesses both output sets. -/
theorem sum_card_siftedSet_mul_card_siftedSet
    (A B₁ B₂ : Finset G) (p : Nat) (hp : p ≠ 0)
    (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty) :
    (∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : Real) *
          (Sifting.siftedSet A B₂ u).card) =
      (B₁.card : Real) * B₂.card *
        ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
  classical
  let corr : G → Real := 𝟭_[A, Real] ○ᵈ 𝟭_[A]
  have hcorr : ∀ x, 0 ≤ corr x := fun x ↦
    dddconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have hraw := Sifting.sum_pairSum_sifted A B₁ B₂ p (fun _ ↦ (1 : Real))
  have hleft :
      (∑ u : Fin p → G,
          Sifting.pairSum (Sifting.siftedSet A B₁ u)
            (Sifting.siftedSet A B₂ u) (fun _ ↦ (1 : Real))) =
        ∑ u : Fin p → G,
          ((Sifting.siftedSet A B₁ u).card : Real) *
            (Sifting.siftedSet A B₂ u).card := by
    apply Finset.sum_congr rfl
    intro u _
    simp [Sifting.pairSum]
  have hright :
      (∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
          (Sifting.commonShiftCount A (b₁ - b₂) : Real) ^ p) =
        ∑ x : G, (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) x * corr x ^ p := by
    rw [sum_dddconv_mul]
    simp [Set.indicator_apply, corr, commonShiftCount_eq_indicatorCorrelation]
  have hweight :
      (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) =
        fun x ↦ (B₁.card : Real) * B₂.card *
          (μ_[Real] B₁ ○ᵈ μ B₂) x := by
    ext x
    simp only [dddconv_eq_sum_sub', Set.indicator_apply, mu_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ B₁ <;> by_cases hyx : y - x ∈ B₂
    · simp only [mem_coe, if_pos hy, if_pos hyx, starRingEnd_apply,
        star_trivial, mul_one]
      have hB₁c : (B₁.card : Real) ≠ 0 := by
        exact_mod_cast hB₁.card_ne_zero
      have hB₂c : (B₂.card : Real) ≠ 0 := by
        exact_mod_cast hB₂.card_ne_zero
      field_simp
    · simp [hy, hyx]
    · simp [hy]
    · simp [hy]
  have hnorm := wLpNorm_pow_eq_sum_norm hp
    (μ_[NNReal] B₁ ○ᵈ μ B₂) corr
  rw [hleft] at hraw
  simp only [mul_one] at hraw
  calc
    (∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : Real) *
          (Sifting.siftedSet A B₂ u).card) =
        ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
          (Sifting.commonShiftCount A (b₁ - b₂) : Real) ^ p := by
      simpa using hraw
    _ =
        ∑ x : G, (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) x * corr x ^ p := by
      exact hright
    _ = (B₁.card : Real) * B₂.card *
          ∑ x : G, (μ_[Real] B₁ ○ᵈ μ B₂) x * corr x ^ p := by
      rw [hweight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (B₁.card : Real) * B₂.card *
        ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
      congr 1
      rw [hnorm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (hcorr x), NNReal.coe_dddconv,
        NNReal.coe_comp_mu, corr]

/-- First moment of one common-tuple sifted set. -/
theorem sum_card_siftedSet (A B : Finset G) (p : Nat) :
    (∑ u : Fin p → G, ((Sifting.siftedSet A B u).card : Real)) =
      (A.card : Real) ^ p * B.card := by
  classical
  have hnat :
      ∑ u : Fin p → G, (Sifting.siftedSet A B u).card =
        A.card ^ p * B.card := by
    simp only [card_eq_sum_indicator_one, Sifting.siftedSet,
      Set.indicator_apply, mem_coe, mem_filter, mem_univ, true_and,
      boole_mul, mul_sum, sum_mul, @sum_comm G, Fintype.piFinset_univ,
      sum_pow']
    congr with b
    refine Fintype.sum_equiv (Equiv.subLeft fun _ : Fin p ↦ b) _ _ (fun u ↦ ?_)
    simp only [Equiv.subLeft_apply]
    by_cases hb : b ∈ B
    · simp only [hb, true_and, if_pos, mul_one]
      rw [Fintype.prod_boole]
      simp only [Pi.sub_apply]
      by_cases h : ∀ i : Fin p, b - u i ∈ A <;> simp [h]
    · simp [hb]
  exact_mod_cast hnat

/-- A common shift tuple simultaneously gives both sifting density bounds.
The proof is the high-product tail selection from dependent random choice,
kept separate so that the common-tuple support information remains usable. -/
theorem exists_common_sifted_density
    (A B₁ B₂ : Finset G) (p : Nat) (hpTwo : 2 ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ u : Fin p → G,
      (Sifting.siftedSet A B₁ u).Nonempty ∧
      (Sifting.siftedSet A B₂ u).Nonempty ∧
      siftingDensityLower A B₁ B₂ p ≤
        ((Sifting.siftedSet A B₁ u).card : Real) / B₁.card ∧
      siftingDensityLower A B₁ B₂ p ≤
        ((Sifting.siftedSet A B₂ u).card : Real) / B₂.card := by
  classical
  have hp : p ≠ 0 := by omega
  have hB₁ : B₁.Nonempty := hB.mono inter_subset_left
  have hB₂ : B₂.Nonempty := hB.mono inter_subset_right
  have hAne : A.Nonempty := hA
  let A₁ : (Fin p → G) → Finset G := fun u ↦ Sifting.siftedSet A B₁ u
  let A₂ : (Fin p → G) → Finset G := fun u ↦ Sifting.siftedSet A B₂ u
  let N : Real := ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]
  let g : (Fin p → G) → Real := fun u ↦ (A₁ u).card * (A₂ u).card
  have hg : ∀ u, 0 ≤ g u := fun u ↦ by dsimp [g]; positivity
  have hgB : ∑ u, g u = (B₁.card : Real) * B₂.card * N ^ p := by
    simpa [g, A₁, A₂, N] using
      sum_card_siftedSet_mul_card_siftedSet A B₁ B₂ p hp hB₁ hB₂
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a, ha⟩ := hA
  let u₀ : Fin p → G := fun _ ↦ b - a
  have hA₁u₀ : b ∈ A₁ u₀ := by
    simp only [A₁, Sifting.mem_siftedSet, u₀]
    refine ⟨(inter_subset_left hb), ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hA₂u₀ : b ∈ A₂ u₀ := by
    simp only [A₂, Sifting.mem_siftedSet, u₀]
    refine ⟨(inter_subset_right hb), ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hsumPos : 0 < ∑ u, g u := by
    exact Finset.sum_pos' (fun u _ ↦ hg u) ⟨u₀, Finset.mem_univ _, by
      dsimp only [g]
      exact mul_pos (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₁u₀⟩))
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₂u₀⟩))⟩
  have hNp : 0 < N ^ p := by
    have hcards : 0 < (B₁.card : Real) * B₂.card := by positivity
    rw [hgB] at hsumPos
    rcases mul_pos_iff.mp hsumPos with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hcards.le hneg.1).elim
  let M : Real :=
    2⁻¹ * N ^ p * (Real.sqrt B₁.card * Real.sqrt B₂.card) /
      (A.card : Real) ^ p
  have hM : 0 < M := by
    dsimp [M]
    have hAc : (0 : Real) < A.card := by exact_mod_cast hAne.card_pos
    have hB₁c : (0 : Real) < B₁.card := by exact_mod_cast hB₁.card_pos
    have hB₂c : (0 : Real) < B₂.card := by exact_mod_cast hB₂.card_pos
    exact div_pos (mul_pos (mul_pos (by norm_num) hNp)
      (mul_pos (Real.sqrt_pos.2 hB₁c) (Real.sqrt_pos.2 hB₂c)))
      (pow_pos hAc p)
  have hsumOne : ∑ u, ((A₁ u).card : Real) = (A.card : Real) ^ p * B₁.card := by
    simpa [A₁] using sum_card_siftedSet A B₁ p
  have hsumTwo : ∑ u, ((A₂ u).card : Real) = (A.card : Real) ^ p * B₂.card := by
    simpa [A₂] using sum_card_siftedSet A B₂ p
  have hhigh : ∃ u, M ^ 2 ≤ g u := by
    by_cases h : ∀ u, g u ≠ 0 → M ^ 2 ≤ g u
    · have hne : ∃ u, g u ≠ 0 := by
        by_contra hn
        push_neg at hn
        have : ∑ u, g u = 0 := by simp [hn]
        linarith
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, h u hu⟩
    · push_neg at h
      obtain ⟨u₁, hu₁ne, hu₁low⟩ := h
      have hlow : (2 : Real) * ∑ u with g u < M ^ 2, g u < ∑ u, g u := by
        rw [← lt_div_iff₀' (by norm_num : (0 : Real) < 2), div_eq_inv_mul]
        calc
          ∑ u with g u < M ^ 2, g u =
              ∑ u with g u < M ^ 2 ∧ g u ≠ 0,
                Real.sqrt (g u) * Real.sqrt (g u) := by
            simp_rw [Real.mul_self_sqrt (hg _), ← Finset.filter_filter,
              Finset.sum_filter_ne_zero]
          _ < ∑ u with g u < M ^ 2 ∧ g u ≠ 0,
                M * Real.sqrt (g u) := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact ⟨u₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁low, hu₁ne⟩⟩
            · intro u hu
              have hgu := (Finset.mem_filter.mp hu).2.1
              have hgne := (Finset.mem_filter.mp hu).2.2
              exact mul_lt_mul_of_pos_right ((Real.sqrt_lt' hM).2 hgu)
                (Real.sqrt_pos.2 ((hg u).lt_of_ne' hgne))
          _ ≤ ∑ u, M * Real.sqrt (g u) :=
            Finset.sum_le_univ_sum_of_nonneg fun u ↦ by positivity
          _ = M * (∑ u, Real.sqrt ((A₁ u).card) *
                Real.sqrt ((A₂ u).card)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            dsimp only [g]
            rw [Real.sqrt_mul (by positivity : (0 : Real) ≤ (A₁ u).card)]
          _ ≤ M * (Real.sqrt (∑ u, ((A₁ u).card : Real)) *
                Real.sqrt (∑ u, ((A₂ u).card : Real))) := by
            gcongr
            exact Real.sum_sqrt_mul_sqrt_le _ (fun _ ↦ by positivity)
              (fun _ ↦ by positivity)
          _ = (2 : Real)⁻¹ * ∑ u, g u := by
            dsimp only [M]
            rw [hsumOne, hsumTwo, Real.sqrt_mul' _ (by positivity),
              Real.sqrt_mul' _ (by positivity),
              mul_mul_mul_comm (Real.sqrt _), Real.mul_self_sqrt,
              ← mul_assoc, div_mul_cancel₀, ← Real.sqrt_mul,
              mul_assoc, Real.mul_self_sqrt, hgB, mul_right_comm, mul_assoc]
            all_goals positivity
      by_contra hnone
      push_neg at hnone
      have hpartition : ∑ u, g u = ∑ u with g u < M ^ 2, g u := by
        congr 1
        symm
        exact Finset.filter_eq_self.mpr (fun u _ ↦ hnone u)
      rw [hpartition] at hlow
      linarith
  obtain ⟨u, hu⟩ := hhigh
  have hprod : siftingDensityLower A B₁ B₂ p ≤
      (((A₁ u).card : Real) / B₁.card) *
        (((A₂ u).card : Real) / B₂.card) := by
    dsimp [siftingDensityLower, M, N, g] at hu ⊢
    have hAc : (A.card : Real) ≠ 0 := by exact_mod_cast hAne.card_ne_zero
    have hB₁c : (B₁.card : Real) ≠ 0 := by exact_mod_cast hB₁.card_ne_zero
    have hB₂c : (B₂.card : Real) ≠ 0 := by exact_mod_cast hB₂.card_ne_zero
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    simpa [mul_pow, div_pow, pow_mul', show (2 : Real) ^ 2 = 4 by norm_num,
      Real.sq_sqrt (show 0 ≤ (B₁.card : Real) by positivity),
      Real.sq_sqrt (show 0 ≤ (B₂.card : Real) by positivity),
      hAc, hB₁c, hB₂c, mul_div_right_comm] using hu
  have hguPos : 0 < g u := (sq_pos_of_pos hM).trans_le hu
  have hcardsPos : 0 < ((A₁ u).card : Real) * (A₂ u).card := by
    simpa only [g] using hguPos
  have hpairs : 0 < ((A₁ u).card : Real) ∧ 0 < ((A₂ u).card : Real) := by
    rcases mul_pos_iff.mp hcardsPos with hpos | hneg
    · exact hpos
    · exact (not_lt_of_ge (Nat.cast_nonneg _) hneg.1).elim
  have hA₁pos : 0 < ((A₁ u).card : Real) := hpairs.1
  have hA₂pos : 0 < ((A₂ u).card : Real) := hpairs.2
  refine ⟨u, Finset.card_pos.mp (by exact_mod_cast hA₁pos),
    Finset.card_pos.mp (by exact_mod_cast hA₂pos), ?_, ?_⟩
  · have hcard₂ : ((A₂ u).card : Real) ≤ B₂.card := by
      exact_mod_cast Finset.card_le_card (Sifting.siftedSet_subset A B₂ u)
    exact hprod.trans (mul_le_of_le_one_right (by positivity)
      ((div_le_one (by positivity : (0 : Real) < B₂.card)).2 hcard₂))
  · have hcard₁ : ((A₁ u).card : Real) ≤ B₁.card := by
      exact_mod_cast Finset.card_le_card (Sifting.siftedSet_subset A B₁ u)
    exact hprod.trans (mul_le_of_le_one_left (by positivity)
      ((div_le_one (by positivity : (0 : Real) < B₁.card)).2 hcard₁))

/-- Concrete sifting output, including the two quantitative density bounds
which are needed when localized almost-periodicity is converted into a
Bohr-child size estimate. -/
structure SiftedPopularData (A B₁ B₂ : Finset G)
    (p : Nat) (epsilon delta : Real) where
  A₁ : Finset G
  A₂ : Finset G
  subset_one : A₁ ⊆ B₁
  subset_two : A₂ ⊆ B₂
  popular_mass : 1 - delta ≤
    LocalizedAlmostPeriodicity.countingInner
      (LocalizedAlmostPeriodicity.differenceConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
        (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
      (LocalizedAlmostPeriodicity.setIndicator (s p epsilon B₁ B₂ A))
  density_one : siftingDensityLower A B₁ B₂ p ≤
    (A₁.card : Real) / B₁.card
  density_two : siftingDensityLower A B₁ B₂ p ≤
    (A₂.card : Real) / B₂.card

namespace SiftedPopularData

/-- The global APAP popular set intersected with the actual base-pair
difference support.  This is the set used in local almost-periodicity:
its cardinality is controlled by the two local base sets rather than by the
ambient group. -/
def supportedPopularSet
    (A B₁ B₂ : Finset G) (p : Nat) (epsilon : Real) : Finset G :=
  _root_.Erdos140.s p epsilon B₁ B₂ A ∩ (B₁ - B₂)

theorem supportedPopularSet_subset_sub
    (A B₁ B₂ : Finset G) (p : Nat) (epsilon : Real) :
    supportedPopularSet A B₁ B₂ p epsilon ⊆ B₁ - B₂ :=
  Finset.inter_subset_right

/-- Positive retained mass forces both sifted sets to be genuine nonempty
sets.  This small fact is essential before they may be used as probability
indicators by localized almost-periodicity. -/
theorem output_nonempty
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1) : data.A₁.Nonempty ∧ data.A₂.Nonempty := by
  have hmass : 1 - delta ≤
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.popular_mass
  constructor
  · by_contra hnonempty
    have hempty : data.A₁ = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty] at hmass
    simp [mu_apply] at hmass
    linarith
  · by_contra hnonempty
    have hempty : data.A₂ = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty] at hmass
    simp [mu_apply] at hmass
    linarith

/-- Intersecting the popular set with B₁-B₂ does not change the retained
mass, because every difference carrying μ_A₁ ○ μ_A₂ already lies there. -/
theorem supported_popular_mass
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta) :
    1 - delta ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂))
        (LocalizedAlmostPeriodicity.setIndicator
          (supportedPopularSet A B₁ B₂ p epsilon)) := by
  have hglobal : 1 - delta ≤
      ∑ x ∈ _root_.Erdos140.s p epsilon B₁ B₂ A,
        (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.popular_mass
  have hsum :
      ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x =
        ∑ x ∈ _root_.Erdos140.s p epsilon B₁ B₂ A,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hxGlobal hxNot
    rw [← not_ne_iff]
    intro hxNe
    apply hxNot
    have hxSupport :
        x ∈ Function.support (μ_[Real] data.A₁ ○ᵈ μ data.A₂) := hxNe
    have hxDiff : x ∈ data.A₁ - data.A₂ := by
      simpa only [support_dddconv mu_nonneg mu_nonneg, support_mu,
        ← coe_sub, mem_coe] using hxSupport
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := Finset.mem_sub.mp hxDiff
    exact Finset.mem_inter.mpr ⟨hxGlobal,
      Finset.mem_sub.mpr ⟨a₁, data.subset_one ha₁, a₂,
        data.subset_two ha₂, hxa⟩⟩
  rw [countingInner_difference_setIndicator_eq_sum, hsum]
  exact hglobal

/-- Positive supported popular mass makes the support-restricted popular set
nonempty. -/
theorem supportedPopularSet_nonempty
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1) :
    (supportedPopularSet A B₁ B₂ p epsilon).Nonempty := by
  by_contra hnone
  have hempty : supportedPopularSet A B₁ B₂ p epsilon = ∅ :=
    not_nonempty_iff_eq_empty.mp hnone
  have hmass := data.supported_popular_mass
  rw [hempty] at hmass
  simp [LocalizedAlmostPeriodicity.countingInner,
    LocalizedAlmostPeriodicity.setIndicator] at hmass
  linarith

end SiftedPopularData

/-- Direct, lossless invocation of sifting.  Unlike the lighter wrapper
below, this certificate retains the two `1/4` density estimates. -/
theorem exists_sifted_popular_data
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hmass, hden₁, hden₂⟩ :=
    Sifting.popularDifferences B₁ B₂ hepsilon hepsilonOne hdelta hp hpTwo
      hpEpsilon hB hA hbad
  refine ⟨{
    A₁ := A₁
    A₂ := A₂
    subset_one := hA₁
    subset_two := hA₂
    popular_mass := ?_
    density_one := ?_
    density_two := ?_ }⟩
  · rwa [countingInner_difference_setIndicator_eq_sum]
  · simpa only [siftingDensityLower] using hden₁
  · simpa only [siftingDensityLower] using hden₂

/-- In the complementary sifting branch, choose the two sifted sets from a
single high-product tuple.  Their whole difference support lies in `A-A`,
so the absence of an exceptional supported difference makes their popular
mass exactly one. -/
theorem exists_sifted_popular_data_of_no_bad
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hdelta : 0 < delta) (hpTwo : 2 ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hsupport : ∀ x, x ∈ B₁ - B₂ → x ∈ A - A →
      x ∈ s p epsilon B₁ B₂ A) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  classical
  obtain ⟨u, hA₁, hA₂, hden₁, hden₂⟩ :=
    exists_common_sifted_density A B₁ B₂ p hpTwo hB hA
  let A₁ := Sifting.siftedSet A B₁ u
  let A₂ := Sifting.siftedSet A B₂ u
  have hsub₁ : A₁ ⊆ B₁ := Sifting.siftedSet_subset A B₁ u
  have hsub₂ : A₂ ⊆ B₂ := Sifting.siftedSet_subset A B₂ u
  have hp : 0 < p := by omega
  let i : Fin p := ⟨0, hp⟩
  have hdiff : A₁ - A₂ ⊆ s p epsilon B₁ B₂ A := by
    intro x hx
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := Finset.mem_sub.mp hx
    apply hsupport x
    · exact Finset.mem_sub.mpr ⟨a₁, hsub₁ ha₁, a₂, hsub₂ ha₂, hxa⟩
    · have ha₁A := (Sifting.mem_siftedSet.mp ha₁).2 i
      have ha₂A := (Sifting.mem_siftedSet.mp ha₂).2 i
      refine Finset.mem_sub.mpr ⟨a₁ - u i, ha₁A, a₂ - u i, ha₂A, ?_⟩
      rw [← hxa]
      abel
  have hsum :
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] A₁ ○ᵈ μ A₂) x = 1 := by
    calc
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] A₁ ○ᵈ μ A₂) x =
          ∑ x : G, (μ_[Real] A₁ ○ᵈ μ A₂) x := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hxnot
        rw [← not_ne_iff]
        intro hxne
        apply hxnot
        apply hdiff
        have hxmem : x ∈ Function.support (μ_[Real] A₁ ○ᵈ μ A₂) := hxne
        simpa only [support_dddconv mu_nonneg mu_nonneg, support_mu,
          ← coe_sub, mem_coe] using hxmem
      _ = 1 := by
        rw [sum_dddconv]
        simp only [starRingEnd_apply, star_trivial]
        rw [sum_mu _ (by simpa [A₁] using hA₁),
          sum_mu _ (by simpa [A₂] using hA₂), one_mul]
  refine ⟨{
    A₁ := A₁
    A₂ := A₂
    subset_one := hsub₁
    subset_two := hsub₂
    popular_mass := ?_
    density_one := by simpa [A₁] using hden₁
    density_two := by simpa [A₂] using hden₂ }⟩
  rw [countingInner_difference_setIndicator_eq_sum, hsum]
  linarith

/-- Unconditional localized sifting: the exceptional-difference branch is
the public DRC theorem, while its complement is the common-tuple
construction above. -/
theorem exists_sifted_popular_data_unconditional
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  classical
  by_cases hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A
  · exact exists_sifted_popular_data B₁ B₂ hepsilon hepsilonOne
      hdelta hp hpTwo hpEpsilon hB hA hbad
  · apply exists_sifted_popular_data_of_no_bad B₁ B₂ hdelta hpTwo hB hA
    intro x hxB hxA
    by_contra hxS
    exact hbad ⟨x, hxB, hxA, hxS⟩

/-- The exact interface between sifting and the relative Fourier
almost-periodicity construction.  It records an actual rank-regular Bohr
datum, its subordination and relative-cardinality estimates, and the
pointwise triple-sum error which localized smoothing consumes.  None of the
fields asserts a density increment or a progression-count conclusion. -/
structure LocalizedSiftingPackage
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (parent : BohrData G) (parentWidth : NNReal)
    (source : Finset G) (rankCost cardMultiplier : Nat)
    (approximationError : Real) where
  child : BohrData G
  child_regular : child.IsRankRegular
  rank_bound : child.rank ≤ parent.rank + rankCost
  subordinate : child.carrier ⊆ (parent.dilate parentWidth).carrier
  relative_card : source.card ≤ cardMultiplier * child.carrier.card
  triple_error : ∀ t ∈ child.carrier,
    |LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂ (s p epsilon B₁ B₂ A) t -
      LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂ (s p epsilon B₁ B₂ A) 0| ≤
      approximationError * (data.A₁.card : Real) * data.A₂.card

/-- Enlarge the three numerical budgets of a localized sifting package.
This is the adapter used after the existential Croot--Sisask/Chang output is
dominated by the uniform rank, volume, and error budgets of a stopping step. -/
def LocalizedSiftingPackage.mono
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    {data : SiftedPopularData A B₁ B₂ p epsilon delta}
    {parent : BohrData G} {parentWidth : NNReal} {source : Finset G}
    {rankCost cardMultiplier rankCost' cardMultiplier' : Nat}
    {approximationError approximationError' : Real}
    (P : LocalizedSiftingPackage data parent parentWidth source
      rankCost cardMultiplier approximationError)
    (hrank : rankCost ≤ rankCost')
    (hcard : cardMultiplier ≤ cardMultiplier')
    (herror : approximationError ≤ approximationError') :
    LocalizedSiftingPackage data parent parentWidth source
      rankCost' cardMultiplier' approximationError' where
  child := P.child
  child_regular := P.child_regular
  rank_bound := P.rank_bound.trans (Nat.add_le_add_left hrank _)
  subordinate := P.subordinate
  relative_card := P.relative_card.trans
    (Nat.mul_le_mul_right P.child.carrier.card hcard)
  triple_error := by
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.Erdos140.s p epsilon B₁ B₂ A) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.Erdos140.s p epsilon B₁ B₂ A) 0|
          ≤ approximationError * (data.A₁.card : Real) * data.A₂.card :=
        P.triple_error t ht
      _ ≤ approximationError' * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- Support-restricted analogue of LocalizedSiftingPackage.  Its triple
error is stated on the actual pair-difference support, so local AP and Chang
see only a set whose size is controlled by B₁-B₂. -/
structure SupportedLocalizedSiftingPackage
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (parent : BohrData G) (parentWidth : NNReal)
    (source : Finset G) (rankCost cardMultiplier : Nat)
    (approximationError : Real) where
  child : BohrData G
  child_regular : child.IsRankRegular
  rank_bound : child.rank ≤ parent.rank + rankCost
  subordinate : child.carrier ⊆ (parent.dilate parentWidth).carrier
  relative_card : source.card ≤ cardMultiplier * child.carrier.card
  triple_error : ∀ t ∈ child.carrier,
    |LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂
          (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) t -
      LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂
          (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) 0| ≤
      approximationError * (data.A₁.card : Real) * data.A₂.card

/-- Enlarge the numerical budgets of a support-restricted localized package. -/
def SupportedLocalizedSiftingPackage.mono
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    {data : SiftedPopularData A B₁ B₂ p epsilon delta}
    {parent : BohrData G} {parentWidth : NNReal} {source : Finset G}
    {rankCost cardMultiplier rankCost' cardMultiplier' : Nat}
    {approximationError approximationError' : Real}
    (P : SupportedLocalizedSiftingPackage data parent parentWidth source
      rankCost cardMultiplier approximationError)
    (hrank : rankCost ≤ rankCost')
    (hcard : cardMultiplier ≤ cardMultiplier')
    (herror : approximationError ≤ approximationError') :
    SupportedLocalizedSiftingPackage data parent parentWidth source
      rankCost' cardMultiplier' approximationError' where
  child := P.child
  child_regular := P.child_regular
  rank_bound := P.rank_bound.trans (Nat.add_le_add_left hrank _)
  subordinate := P.subordinate
  relative_card := P.relative_card.trans
    (Nat.mul_le_mul_right P.child.carrier.card hcard)
  triple_error := by
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) 0|
          ≤ approximationError * (data.A₁.card : Real) * data.A₂.card :=
        P.triple_error t ht
      _ ≤ approximationError' * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- APAP's smoothed probability convolution is exactly the discrete
counting convolution used by the sifting and adjoint identities. -/
theorem sumConvolution_probability_difference_eq
    (D A₁ A₂ : Finset G) :
    LocalizedAlmostPeriodicity.sumConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator D)
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator A₂)) =
      μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂) := by
  funext x
  rw [probabilityIndicator_eq_mu,
    differenceConvolution_probability_eq_dddconv,
    LocalizedAlmostPeriodicity.sumConvolution, ddconv_eq_sum_sub']

/-- Exact set-mass form of the localized smoothed inner product. -/
theorem countingInner_smoothed_setIndicator_eq_sum
    (D A₁ A₂ S : Finset G) :
    LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S) =
      ∑ x ∈ S, (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
  classical
  rw [sumConvolution_probability_difference_eq]
  unfold LocalizedAlmostPeriodicity.countingInner
    LocalizedAlmostPeriodicity.setIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun x : G ↦ x ∈ S) = S := by ext; simp
  rw [hfilter]

/-- A lower bound for smoothed mass on a superlevel set gives the
corresponding lower bound for the full correlation inner product.  This is
the positivity half of the adjoint step and keeps every counting
normalization explicit. -/
theorem smoothed_superlevel_inner_lower_bound
    {D A₁ A₂ S : Finset G} {corr : G → Real}
    {mass threshold : Real}
    (hthreshold : 0 ≤ threshold)
    (hcorr : ∀ x, 0 ≤ corr x)
    (hpopular : ∀ x ∈ S, threshold ≤ corr x)
    (hmass : mass ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S)) :
    threshold * mass ≤
      ∑ x : G, (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
  classical
  rw [countingInner_smoothed_setIndicator_eq_sum] at hmass
  have hf_nonneg : ∀ x : G,
      0 ≤ (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
    intro x
    exact ddconv_apply_nonneg mu_nonneg
      (fun y ↦ dddconv_apply_nonneg mu_nonneg mu_nonneg y) x
  calc
    threshold * mass ≤
        threshold * ∑ x ∈ S,
          (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x :=
      mul_le_mul_of_nonneg_left hmass hthreshold
    _ = ∑ x ∈ S,
        threshold * (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S,
        (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [mul_comm threshold]
      exact mul_le_mul_of_nonneg_left (hpopular x hx) (hf_nonneg x)
    _ ≤ ∑ x : G,
        (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
      exact Finset.sum_le_univ_sum_of_nonneg fun x ↦
        mul_nonneg (hf_nonneg x) (hcorr x)

/-- A finite probability-weighted average cannot exceed every value of the
averaged function.  The witness is chosen at a genuine maximum of the
finite ambient group. -/
theorem exists_value_ge_probability_average
    {w f : G → Real} (hw : ∀ x, 0 ≤ w x)
    (hwsum : ∑ x : G, w x = 1) {lower : Real}
    (hlower : lower ≤ ∑ x : G, w x * f x) :
    ∃ x : G, lower ≤ f x := by
  classical
  obtain ⟨x, _hx, hxmax⟩ :=
    Finset.exists_max_image Finset.univ f (Finset.univ_nonempty :
      (Finset.univ : Finset G).Nonempty)
  refine ⟨x, hlower.trans ?_⟩
  calc
    ∑ y : G, w y * f y ≤ ∑ y : G, w y * f x := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hxmax y (by simp)) (hw y)
    _ = f x := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- Support-sensitive form of finite probability selection.  This keeps the
selected point inside the finite support, which is essential when the point
is subsequently represented as a difference of two Bohr-carrier elements. -/
theorem exists_value_ge_probability_average_on
    {w f : G → Real} {T : Finset G} (hT : T.Nonempty)
    (hw : ∀ x, 0 ≤ w x) (hwsupport : ∀ x, x ∉ T → w x = 0)
    (hwsum : ∑ x : G, w x = 1) {lower : Real}
    (hlower : lower ≤ ∑ x : G, w x * f x) :
    ∃ x ∈ T, lower ≤ f x := by
  classical
  obtain ⟨x, hxT, hxmax⟩ := Finset.exists_max_image T f hT
  refine ⟨x, hxT, hlower.trans ?_⟩
  calc
    ∑ y : G, w y * f y ≤ ∑ y : G, w y * f x := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ T
      · exact mul_le_mul_of_nonneg_left (hxmax y hy) (hw y)
      · rw [hwsupport y hy, zero_mul, zero_mul]
    _ = f x := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- The localized-unbalancing weight admits the cross-difference
factorization used to select the translate in the sifting argument. -/
theorem coe_smoothingWeight_eq_crossDifference
    (D E : Finset G) :
    ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E : G → Real) =
      (μ_[Real] D ○ᵈ μ E) ∗ᵈ (μ E ○ᵈ μ D) := by
  unfold LocalizedUnbalancing.smoothingWeight
    LocalizedUnbalancing.smoothingBase
  simp only [NNReal.coe_comp_dddconv, NNReal.coe_comp_ddconv,
    NNReal.coe_comp_mu]
  symm
  rw [dddconv_ddconv_dddconv_comm, ddconv_comm (μ_[Real] E) (μ D)]

/-- Expanding the cross-difference factorization writes the high moment as
an average of moments against translated finite difference measures. -/
theorem smoothingWeight_absMoment_eq_crossAverage
    (D E : Finset G) (f : G → Real) (p : Nat) :
    weightedAbsMoment
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) f p =
      ∑ z : G, (μ_[Real] D ○ᵈ μ E) z *
        weightedAbsMoment
          (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) f p := by
  rw [coe_smoothingWeight_eq_crossDifference]
  unfold weightedAbsMoment
  simp_rw [ddconv_eq_sum_sub', Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A high moment under the fourfold smoothing weight selects a translate
`z + E` which genuinely meets `D`, while retaining the full moment lower
bound against `μ_(z+E) ○ μ_D`. -/
theorem exists_translated_difference_moment_ge
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (f : G → Real) (p : Nat) {lower : Real}
    (hlower : lower ≤ weightedAbsMoment
      ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) f p) :
    ∃ z ∈ D - E,
      ((z +ᵥ E) ∩ D).Nonempty ∧
      lower ≤ weightedAbsMoment (μ_[Real] (z +ᵥ E) ○ᵈ μ D) f p := by
  let w : G → Real := μ_[Real] D ○ᵈ μ E
  let F : G → Real := fun z ↦
    weightedAbsMoment (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) f p
  have hDE : (D - E).Nonempty := by
    obtain ⟨d, hd⟩ := hD
    obtain ⟨e, he⟩ := hE
    refine ⟨d - e, ?_⟩
    exact Finset.mem_sub.mpr ⟨d, hd, e, he, rfl⟩
  have hw : ∀ z, 0 ≤ w z := by
    intro z
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg z
  have hwsupport : ∀ z, z ∉ D - E → w z = 0 := by
    intro z hz
    rw [← not_ne_iff]
    intro hwz
    apply hz
    have hzsupport : z ∈ Function.support w := hwz
    simpa only [w, support_dddconv mu_nonneg mu_nonneg,
      support_mu, ← coe_sub, mem_coe] using hzsupport
  have hwsum : ∑ z : G, w z = 1 := by
    dsimp only [w]
    rw [sum_dddconv]
    simp only [starRingEnd_apply, star_trivial]
    rw [sum_mu _ hD, sum_mu _ hE, one_mul]
  have haverage : lower ≤ ∑ z : G, w z * F z := by
    rw [← smoothingWeight_absMoment_eq_crossAverage]
    exact hlower
  obtain ⟨z, hz, hzlarge⟩ :=
    exists_value_ge_probability_average_on hDE hw hwsupport hwsum haverage
  obtain ⟨d, hd, e, he, hde⟩ := Finset.mem_sub.mp hz
  refine ⟨z, hz, ?_, ?_⟩
  · refine ⟨d, Finset.mem_inter.mpr ⟨?_, hd⟩⟩
    rw [Finset.mem_vadd_finset]
    refine ⟨e, he, ?_⟩
    rw [← hde]
    simp only [vadd_eq_add, neg_smul, one_smul]
    exact sub_add_cancel d e
  · dsimp only [F] at hzlarge
    have hweight :
        (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) =
          μ_[Real] (z +ᵥ E) ○ᵈ μ D := by
      rw [← translate_mu, translate_dddconv]
      rfl
    rw [hweight] at hzlarge
    exact hzlarge

/-- Norm-form translate selection used directly before sifting. -/
theorem exists_translated_difference_lpNorm_ge
    {D E A : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hA : A.Nonempty) {p : Nat} (hp : 0 < p) {lower : Real}
    (hlowerNonneg : 0 ≤ lower)
    (hlower : lower ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real] A ○ᵈ μ A) p) :
    ∃ z ∈ D - E,
      ((z +ᵥ E) ∩ D).Nonempty ∧
      lower ≤ ‖μ_[Real] A ○ᵈ μ A‖_[p, μ (z +ᵥ E) ○ᵈ μ D] := by
  let nu := LocalizedUnbalancing.smoothingWeight D E
  have hnu : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ nu : G → Real) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact_mod_cast (LocalizedUnbalancing.smoothingWeight_nonneg D E x)
    · simpa using congrArg (fun r : NNReal ↦ (r : Real))
        (LocalizedUnbalancing.smoothingWeight_sum hD hE)
  have hmoment : lower ^ p ≤
      weightedAbsMoment ((↑) ∘ nu : G → Real)
        (μ_[Real] A ○ᵈ μ A) p := by
    calc
      lower ^ p ≤
          BalancedRestriction.weightedLpNorm
              ((↑) ∘ nu : G → Real) (μ_[Real] A ○ᵈ μ A) p ^ p :=
        pow_le_pow_left₀ hlowerNonneg hlower p
      _ = weightedAbsMoment ((↑) ∘ nu : G → Real)
          (μ_[Real] A ○ᵈ μ A) p :=
        BalancedRestriction.weightedLpNorm_pow hnu hp
  obtain ⟨z, hz, hinter, hselected⟩ :=
    exists_translated_difference_moment_ge hD hE
      (μ_[Real] A ○ᵈ μ A) p (by simpa [nu] using hmoment)
  let wsel : G → NNReal := μ_[NNReal] (z +ᵥ E) ○ᵈ μ D
  have hB₁ : (z +ᵥ E).Nonempty := by
    obtain ⟨e, he⟩ := hE
    refine ⟨z + e, ?_⟩
    rw [Finset.mem_vadd_finset]
    exact ⟨e, he, rfl⟩
  have hwsel : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ wsel : G → Real) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact_mod_cast (dddconv_apply_nonneg mu_nonneg mu_nonneg x : 0 ≤ wsel x)
    · dsimp only [wsel]
      simp only [NNReal.coe_comp_dddconv, NNReal.coe_comp_mu]
      rw [sum_dddconv]
      simp only [starRingEnd_apply, star_trivial]
      rw [sum_mu _ hB₁, sum_mu _ hD, one_mul]
  have hselected' : lower ^ p ≤
      weightedAbsMoment ((↑) ∘ wsel : G → Real)
        (μ_[Real] A ○ᵈ μ A) p := by
    simpa only [wsel, NNReal.coe_comp_dddconv, NNReal.coe_comp_mu] using hselected
  have hlocalPow : lower ^ p ≤
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p ^ p := by
    rw [BalancedRestriction.weightedLpNorm_pow hwsel hp]
    exact hselected'
  have hlocalNonneg : 0 ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p :=
    BalancedRestriction.weightedLpNorm_nonneg hwsel _ _
  have hlocal : lower ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p := by
    by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hpwlt := pow_lt_pow_left₀ hlt hlocalNonneg hp.ne'
    exact (not_lt_of_ge hlocalPow) hpwlt
  refine ⟨z, hz, hinter, ?_⟩
  rw [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm wsel
    (μ_[Real] A ○ᵈ μ A) hp] at hlocal
  exact hlocal

/-- The APAP probability convolution is the local translate density divided
by `|A|`.  This is the final normalization conversion before
`narrowLocated`. -/
theorem card_mul_mu_ddconv_eq_localDensity
    {A D : Finset G} (hA : A.Nonempty) (x : G) :
    (A.card : Real) * (μ_[Real] D ∗ᵈ μ A) x = localDensity A D x := by
  classical
  rw [ddconv_eq_sum_sub', localDensity, normalizedConvolution, Finset.mul_sum]
  let e : G ≃ G := Equiv.subLeft x
  rw [Fintype.sum_equiv e
    (fun z : G ↦ (A.card : Real) * (μ_[Real] D z * μ A (x - z)))
    (fun y : G ↦ (A.card : Real) * (μ_[Real] D (x - y) * μ A y))]
  · apply Finset.sum_congr rfl
    intro y _
    simp only [mu_apply, finsetIndicator, normalizedIndicator]
    have hAcard : (A.card : Real) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    by_cases hyA : y ∈ A
    · by_cases hxyD : x - y ∈ D
      · simp only [if_pos hyA, if_pos hxyD, mul_one]
        calc
          (A.card : Real) * ((D.card : Real)⁻¹ * (A.card : Real)⁻¹) =
              (D.card : Real)⁻¹ * ((A.card : Real) * (A.card : Real)⁻¹) := by ring
          _ = (D.card : Real)⁻¹ := by rw [mul_inv_cancel₀ hAcard, mul_one]
          _ = 1 * (D.card : Real)⁻¹ := by rw [one_mul]
      · simp [hyA, hxyD]
    · simp [hyA]
  · intro y
    simp [e]

/-- The exact adjoint identity at the heart of the localized density step.
It moves the smoothed difference convolution from the popular-difference
side onto the original set, leaving a nonnegative probability weight. -/
theorem smoothed_correlation_adjoint
    (d a₁ a₂ a : G → Real) :
    ⟪d ∗ᵈ (a₁ ○ᵈ a₂), a ○ᵈ a⟫_[Real] =
      ⟪d ∗ᵈ a, (a₂ ○ᵈ a₁) ∗ᵈ a⟫_[Real] := by
  rw [ddconv_wInner_one, ddconv_wInner_one]
  congr 1
  change (a ○ᵈ a) ○ᵈ (a₁ ○ᵈ a₂) = ((a₂ ○ᵈ a₁) ∗ᵈ a) ○ᵈ a
  simp_rw [← ddconv_conjneg, conjneg_ddconv, conjneg_conjneg]
  calc
    (a ∗ᵈ conjneg a) ∗ᵈ (conjneg a₁ ∗ᵈ a₂) =
        (a ∗ᵈ conjneg a₁) ∗ᵈ (conjneg a ∗ᵈ a₂) :=
      ddconv_ddconv_ddconv_comm _ _ _ _
    _ = (conjneg a₁ ∗ᵈ a) ∗ᵈ (a₂ ∗ᵈ conjneg a) := by
      rw [ddconv_comm a, ddconv_comm (conjneg a) a₂]
    _ = (conjneg a₁ ∗ᵈ a₂) ∗ᵈ (a ∗ᵈ conjneg a) :=
      ddconv_ddconv_ddconv_comm _ _ _ _
    _ = ((a₂ ∗ᵈ conjneg a₁) ∗ᵈ a) ∗ᵈ conjneg a := by
      rw [ddconv_comm (conjneg a₁) a₂]
      exact (ddconv_assoc _ _ _).symm

/-- The complete adjoint-selection step.  A smoothed popular-difference
mass supplies a genuine translate on which the original set has the
corresponding local density.  The conclusion is about an actual group
element and an actual finite carrier, not an `L∞` surrogate. -/
theorem exists_localDensity_ge_of_smoothed_superlevel
    {D A₁ A₂ A S : Finset G}
    (hD : D.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hA : A.Nonempty)
    {threshold mass lower : Real} (hthreshold : 0 ≤ threshold)
    (hcorr : ∀ x, 0 ≤ (μ_[Real] A ○ᵈ μ A) x)
    (hpopular : ∀ x ∈ S, threshold ≤ (μ_[Real] A ○ᵈ μ A) x)
    (hmass : mass ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S))
    (hlower : lower ≤ threshold * mass) :
    ∃ x : G, (A.card : Real) * lower ≤ localDensity A D x := by
  have hsmoothed := smoothed_superlevel_inner_lower_bound hthreshold hcorr
    hpopular hmass
  have hadjoint := smoothed_correlation_adjoint
    (μ_[Real] D) (μ A₁) (μ A₂) (μ A)
  rw [RCLike.wInner_one_eq_sum, RCLike.wInner_one_eq_sum] at hadjoint
  simp only [RCLike.inner_apply', RCLike.conj_to_real] at hadjoint
  let w : G → Real := (μ_[Real] A₂ ○ᵈ μ A₁) ∗ᵈ μ A
  let f : G → Real := μ_[Real] D ∗ᵈ μ A
  have hw : ∀ x, 0 ≤ w x := by
    intro x
    exact ddconv_apply_nonneg
      (fun y ↦ dddconv_apply_nonneg mu_nonneg mu_nonneg y) mu_nonneg x
  have hwsum : ∑ x : G, w x = 1 := by
    dsimp only [w]
    rw [sum_ddconv, sum_dddconv]
    simp only [starRingEnd_apply, star_trivial]
    rw [sum_mu _ hA₂, sum_mu _ hA₁, one_mul,
      sum_mu _ hA, mul_one]
  have havg : lower ≤ ∑ x : G, w x * f x := by
    calc
      lower ≤ threshold * mass := hlower
      _ ≤ ∑ x : G,
          (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * (μ A ○ᵈ μ A) x :=
        hsmoothed
      _ = ∑ x : G, w x * f x := by
        rw [hadjoint]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm]
  obtain ⟨x, hx⟩ := exists_value_ge_probability_average hw hwsum havg
  refine ⟨x, ?_⟩
  rw [← card_mul_mu_ddconv_eq_localDensity hA]
  exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)

end SiftingOutput

theorem narrowingSet_nonempty_of_localDensity_pos
    {A C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : 0 < localDensity A C x) :
    (narrowingSet A C x).Nonempty := by
  by_contra h
  have hcardNot : ¬ 0 < (narrowingSet A C x).card := by
    intro hcard
    exact h (Finset.card_pos.mp hcard)
  have hcard : (narrowingSet A C x).card = 0 := Nat.eq_zero_of_not_pos hcardNot
  rw [localDensity_eq_card_narrowingSet_div hC, hcard] at hx
  norm_num at hx

/-! ## Making a genuine next restriction -/

/-- A regular child shell which can be used as the next ambient carrier. -/
structure RegularChild where
  bohr : BohrData G
  outer : NNReal
  inner : NNReal
  regular : 0 < inner ∧ inner ≤ outer ∧
    (bohr.dilate (outer + inner)).carrier.card ≤
      2 * (bohr.dilate (outer - inner)).carrier.card

namespace RegularChild

def carrier (c : RegularChild (G := G)) : Finset G :=
  (c.bohr.dilate c.outer).carrier

lemma carrier_nonempty (c : RegularChild (G := G)) : c.carrier.Nonempty :=
  (c.bohr.dilate c.outer).carrier_nonempty

def asRestriction (c : RegularChild (G := G))
    (A : Finset G) (hA : A.Nonempty) (hAcarrier : A ⊆ c.carrier) :
    RegularRestriction G where
  bohr := c.bohr
  outer := c.outer
  inner := c.inner
  regular := c.regular
  set := A
  nonempty := hA
  subset_carrier := hAcarrier

/-- A rank-regular datum is already a valid regular child at its unit
carrier.  The explicit `1/(400 max(rank,1))` inner width turns the two
rank-regular cardinality estimates into the required factor-two shell
bound. -/
theorem exists_of_rankRegular (B : BohrData G) (hreg : B.IsRankRegular) :
    ∃ c : RegularChild (G := G),
      c.bohr = B ∧ c.outer = 1 ∧ c.carrier = B.carrier := by
  let d : Nat := max B.rank 1
  let kappa : NNReal := 1 / (400 * (d : NNReal))
  have hd : 0 < d := by simp [d]
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hkappaReg : kappa ≤ 1 / (100 * (d : NNReal)) := by
    dsimp [kappa]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num : (100 : NNReal) ≤ 400)
      (by positivity)
  have hkappaOne : kappa ≤ 1 := by
    apply hkappaReg.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hcards := hreg kappa (by simpa [d] using hkappaReg)
  have hquarter : (100 : Real) * d * (kappa : Real) ≤ 1 / 4 := by
    have hkappaReal : (kappa : Real) ≤ 1 / (400 * (d : Real)) := by
      exact_mod_cast (show kappa ≤ 1 / (400 * (d : NNReal)) by rfl)
    have hdReal : (0 : Real) < d := by exact_mod_cast hd
    calc
      (100 : Real) * d * (kappa : Real) ≤
          100 * d * (1 / (400 * (d : Real))) := by gcongr
      _ = 1 / 4 := by field_simp; ring
  have hcardReal :
      ((B.dilate (1 + kappa)).carrier.card : Real) ≤
        2 * ((B.dilate (1 - kappa)).carrier.card : Real) := by
    nlinarith [hcards.1, hcards.2, hquarter,
      show (0 : Real) < B.carrier.card by
        exact_mod_cast B.carrier_nonempty.card_pos]
  have hcard :
      (B.dilate (1 + kappa)).carrier.card ≤
        2 * (B.dilate (1 - kappa)).carrier.card := by
    exact_mod_cast hcardReal
  let c : RegularChild (G := G) :=
    { bohr := B
      outer := 1
      inner := kappa
      regular := ⟨hkappaPos, hkappaOne, hcard⟩ }
  refine ⟨c, rfl, rfl, ?_⟩
  simp only [carrier, c, BohrData.dilate_one]

end RegularChild

/-- Recenter a dense translate on a regular child carrier, preserving its
exact translation back into the original set. -/
def narrowLocated {original : Finset G} (s : LocatedRestriction original)
    (child : RegularChild (G := G)) (x : G)
    (hpos : 0 < localDensity s.restriction.set child.carrier x) :
    LocatedRestriction original where
  restriction := child.asRestriction
    (narrowingSet s.restriction.set child.carrier x)
    (narrowingSet_nonempty_of_localDensity_pos child.carrier_nonempty hpos)
    (narrowingSet_subset_carrier (B := child.bohr) (rho := child.outer)
      (A := s.restriction.set) (C := child.carrier) (x := x) fun _ h => h)
  shift := s.shift - x
  subset_original := by
    intro z hz
    have hzA := (mem_narrowingSet.mp hz).2
    have hsource := s.subset_original (x + z) hzA
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]

@[simp] theorem density_narrowLocated {original : Finset G}
    (s : LocatedRestriction original) (child : RegularChild (G := G)) (x : G)
    (hpos : 0 < localDensity s.restriction.set child.carrier x) :
    (narrowLocated s child x hpos).density =
      localDensity s.restriction.set child.carrier x := by
  change ((narrowingSet s.restriction.set child.carrier x).card : Real) /
      child.carrier.card = localDensity s.restriction.set child.carrier x
  exact (localDensity_eq_card_narrowingSet_div child.carrier_nonempty x).symm

theorem narrowLocated_isControlledIncrement
    {original : Finset G} (s : LocatedRestriction original)
    (child : RegularChild (G := G)) (x : G)
    {q sizeCost : Real} {rankCost : Nat}
    (hpos : 0 < localDensity s.restriction.set child.carrier x)
    (hdensity : q * s.density ≤
      localDensity s.restriction.set child.carrier x)
    (hrank : child.bohr.rank ≤ s.rank + rankCost)
    (hcard : Real.exp (-sizeCost) * (s.card : Real) ≤ child.carrier.card) :
    IsControlledIncrement q rankCost sizeCost s.restriction
      (narrowLocated s child x hpos).restriction := by
  refine ⟨?_, hrank, ?_⟩
  · change q * s.density ≤
      ((narrowingSet s.restriction.set child.carrier x).card : Real) /
        child.carrier.card
    rw [← localDensity_eq_card_narrowingSet_div child.carrier_nonempty]
    exact hdensity
  · change Real.exp (-sizeCost) * (s.restriction.card : Real) ≤
      child.carrier.card
    exact hcard

section AnalyticLocatedIncrement

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Convert the complex unnormalized threefold almost-period estimate
returned by the final localized Croot--Sisask/Chang theorem into the real
triple-indicator estimate consumed by LocalizedSiftingPackage.  The
translation is evaluated at zero with -t; symmetry of a Bohr carrier is
the only sign input. -/
theorem triple_error_of_threefold_dLinfty
    {D : BohrData G} {A₁ A₂ S : Finset G} {error : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hperiod : ∀ t ∈ D.carrier,
      ‖τ t ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂) -
          ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂)‖_[∞] ≤
        error) :
    ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        error * (A₁.card : Real) * A₂.card := by
  classical
  let F : G → Complex :=
    (μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂
  have hF (u : G) :
      F u = Complex.ofReal
        (LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S u /
          (A₁.card * A₂.card : Real)) := by
    dsimp only [F]
    rw [threefold_eq_ofReal_finiteInner]
    congr 1
    exact LocalizedAlmostPeriodicity.finiteInner_translate_differenceConvolution_eq
      hA₁ hA₂ S u
  intro t ht
  have hneg : -t ∈ D.carrier := BohrData.neg_mem_carrier.mpr ht
  have hpoint :
      ‖(τ (-t) F - F) 0‖ ≤ error := by
    calc
      ‖(τ (-t) F - F) 0‖ ≤ ‖τ (-t) F - F‖_[∞] :=
        norm_le_dLinftyNorm
      _ ≤ error := by simpa only [F] using hperiod (-t) hneg
  have hquot :
      |(LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0) /
          (A₁.card * A₂.card : Real)| ≤ error := by
    rw [Pi.sub_apply, translate_apply, sub_neg_eq_add, zero_add,
      hF t, hF 0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← sub_div] at hpoint
    exact hpoint
  have hcard : (0 : Real) < (A₁.card : Real) * A₂.card :=
    mul_pos (by exact_mod_cast hA₁.card_pos) (by exact_mod_cast hA₂.card_pos)
  rw [abs_div, abs_of_pos hcard] at hquot
  have hscaled := (div_le_iff₀ hcard).mp hquot
  nlinarith

/-- Reflection identity for the normalization-compatible ordering: after
swapping the two normalized sets, the negated popular set stays in the last
slot and the shift parameter changes sign. -/
theorem tripleIndicatorSum_commuted_reflect
    (A₁ A₂ S : Finset G) (t : G) :
    LocalizedAlmostPeriodicity.tripleIndicatorSum A₂ A₁ (-S) t =
      LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S (-t) := by
  classical
  unfold LocalizedAlmostPeriodicity.tripleIndicatorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a₁ _
  apply Finset.sum_congr rfl
  intro a₂ _
  have hind (u : G) :
      LocalizedAlmostPeriodicity.setIndicator (-S) u =
        LocalizedAlmostPeriodicity.setIndicator S (-u) := by
    by_cases hu : u ∈ -S
    · have hneg : -u ∈ S := by simpa using hu
      simp [LocalizedAlmostPeriodicity.setIndicator, hu, hneg]
    · have hneg : -u ∉ S := by
        intro h
        apply hu
        simpa using h
      simp [LocalizedAlmostPeriodicity.setIndicator, hu, hneg]
  rw [hind]
  have harg : -(t + a₂ - a₁) = -t + a₁ - a₂ := by abel
  rw [harg]
  ring

/-- Triple-error bridge for the normalization-compatible commuted
orientation: first factor μ(-A₂), middle factor 1(-S), and last factor
μ(A₁).  This is exactly the reflected triple sum with its original
|A₁||A₂| normalization, so no extra |S|/|A₁| factor is introduced. -/
theorem triple_error_of_commuted_reflected_threefold_dLinfty
    {D : BohrData G} {A₁ A₂ S : Finset G} {error : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hperiod : ∀ t ∈ D.carrier,
      ‖τ t ((μ_[Complex] (-A₂) ∗ᵈ
              (𝟭_[(-S : Finset G)] : G → Complex)) ∗ᵈ μ A₁) -
          ((μ_[Complex] (-A₂) ∗ᵈ
              (𝟭_[(-S : Finset G)] : G → Complex)) ∗ᵈ μ A₁)‖_[∞] ≤
        error) :
    ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        error * (A₁.card : Real) * A₂.card := by
  classical
  have hbase := triple_error_of_threefold_dLinfty
    (D := D) (A₁ := A₂) (A₂ := A₁) (S := -S) (error := error)
    hA₂ hA₁ hperiod
  intro t ht
  have hneg : -t ∈ D.carrier := BohrData.neg_mem_carrier.mpr ht
  have h := hbase (-t) hneg
  rw [tripleIndicatorSum_commuted_reflect A₁ A₂ S (-t),
    tripleIndicatorSum_commuted_reflect A₁ A₂ S 0] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The Croot--Sisask exponent occurring in the localized AP output, named
so quantitative callers can state the retained-set lower bound without
repeating the nested ceiling expression. -/
noncomputable def localizedAPSampleQ (M L : Finset G) : Nat :=
  ⌈1 + Real.log (min 1 ((L.card : Real) / M.card))⁻¹⌉₊

/-- The corresponding Croot--Sisask sample size. -/
noncomputable def localizedAPSampleK
    (M L : Finset G) (approxDelta : Real) (m : Nat) : Nat :=
  crootSisaskSampleSize (localizedAPSampleQ M L)
    ((approxDelta / m) / Real.exp 1)

/-- Support-restricted relative-T constructor with the normalization-compatible
Bloom--Sisask ordering.  The Croot input is -A₂, the unnormalized middle set
is -S, and the final normalized set is A₁.  Consequently the sample exponent
depends on |A₁|/|S|, while the almost-period error transfers directly to the
triple sum without an additional |S|/|A₁| factor. -/
theorem exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses_commuted
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            (((SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma).card : Real) /
              data.A₁.card) ≤ approximationError) :
    ∃ (T X : Finset G) (rho : NNReal) (C₀ : BohrData G)
      (Delta : Finset (AddChar G Complex)),
      ((((-data.A₂).card : Real) ^
            localizedAPSampleK
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              data.A₁ approxDelta m / 2 * B₀.carrier.card) /
          ((-data.A₂ + B₀.carrier).card : Real) ^
            localizedAPSampleK
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              data.A₁ approxDelta m ≤ T.card) ∧
      T ⊆ B₀.carrier ∧ X.Nonempty ∧
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale B₀ T (1 / 2)) ∧
      Nonempty
        (SupportedLocalizedSiftingPackage data C₀ (kappa + kappa)
          (C₀.dilate kappa).carrier Delta.card
          ((qQuant * LocalizedAlmostPeriodicity.spectralQuantization
              (RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
              Delta.card *
            4 ^ (B₀.rank + Delta.card))
          approximationError) := by
  classical
  let S : Finset G :=
    SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma
  have houtputs := data.output_nonempty hdelta
  have hnegA₂ : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  have hS : S.Nonempty := by
    simpa [S] using data.supportedPopularSet_nonempty hdelta
  have hnegS : (-S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨-s, by simpa using hs⟩
  obtain ⟨T, X, z, rho, C₀, Delta, R, hTB₀, _hzT, _hX,
      hXne, hTcard, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub, hRcard,
      hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
      (A := -data.A₂) hnegA₂ approxDelta happroxDelta m hm
      (-S) data.A₁ hnegS houtputs.1 B₀ hB₀reg kappa hkappa
      qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt ((S.card : Real) / data.A₁.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hraw : rawError ≤ approximationError := by
    calc
      rawError ≤
          2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt ((S.card : Real) / data.A₁.card) := by
        dsimp only [rawError]
        gcongr
      _ ≤ approximationError := by simpa [S] using hsmall T Delta hDeltaCard
  refine ⟨T, X, rho, C₀, Delta, ?_, hTB₀, hXne, hDeltaCard,
    hrhoHalf, hrhoOne, hC₀, ⟨?_⟩⟩
  · simpa [S, localizedAPSampleK, localizedAPSampleQ] using hTcard
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_commuted_reflected_threefold_dLinfty
      houtputs.1 houtputs.2 (D := R) (error := rawError) (by
        intro t ht
        simpa [S, n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) 0|
          ≤ rawError * (data.A₁.card : Real) * data.A₂.card := by
            simpa [S] using htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

end AnalyticLocatedIncrement

/-! ## Bourgain narrowing as a concrete count-or-increment step -/

/-- The simultaneous dense-translate alternative left for the analytic
counting argument after Bourgain narrowing. -/
def HasDensePair {original : Finset G} (s : LocatedRestriction original)
    (childOne childTwo : RegularChild (G := G)) (epsilon : Real) : Prop :=
  ∃ x ∈ s.ambient,
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childOne.carrier x ∧
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childTwo.carrier x

/-- All concrete Bohr-geometric data required at one narrowing step.  This
is the interface supplied by the relative Chang--Sanders and localized
almost-periodicity construction: it contains actual Bohr data and actual
cardinality inequalities, not a numerical state or the desired increment. -/
structure NarrowingPackage {original : Finset G}
    (s : LocatedRestriction original) (epsilon sizeCost : Real)
    (rankCost : Nat) where
  eta : NNReal
  plateau : s.restriction.bohr.IsPlateauRegularAt s.restriction.outer eta
  childOne : RegularChild (G := G)
  childTwo : RegularChild (G := G)
  smallOne : childOne.carrier ⊆
    (s.restriction.bohr.dilate eta).carrier
  smallTwo : childTwo.carrier ⊆
    (s.restriction.bohr.dilate eta).carrier
  rankOne : childOne.bohr.rank ≤ s.rank + rankCost
  rankTwo : childTwo.bohr.rank ≤ s.rank + rankCost
  cardOne : Real.exp (-sizeCost) * (s.card : Real) ≤ childOne.carrier.card
  cardTwo : Real.exp (-sizeCost) * (s.card : Real) ≤ childTwo.carrier.card

end

end DensityStep

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/HolderLifting.lean` -/

section
/-!
# The finite Hölder-lifting step for Erdős Problem 140

This file isolates the normalization-sensitive, but otherwise elementary, last
step of the Kelley--Meka/Bloom--Sisask counting argument.  We use natural
moments rather than real powers of a norm.  For `C ⊆ B` the main inequality is

`relativeDensity C B * |<f, muWeight_C>| ^ p ≤ localMoment B p f`.

It is just the triangle inequality followed by Jensen's inequality on the
finite probability space `C`.  The final theorem records the constants used in
the application: the good alternative gives one half of the normalized main
term, while the bad alternative gives a one-quarter lower bound and therefore
contradicts a one-eighth balanced bound.
-/

open scoped BigOperators
open _root_.Finset

namespace HolderLifting

variable {G : Type*} [Fintype G] [AddCommGroup G]

/-- The uniform probability average on the ambient finite type. -/
noncomputable def ambientAverage (f : G → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card G

/-- The `{0,1}`-valued indicator. -/
noncomputable def indicator (C : Finset G) (x : G) : ℝ :=
  open scoped Classical in
  if x ∈ C then 1 else 0

/-- The probability-density normalization `|G| / |C| · 1_C`. -/
noncomputable def normalizedIndicator (C : Finset G) (x : G) : ℝ :=
  (Fintype.card G : ℝ) / C.card * indicator C x

/-- The uniform average on a nonempty finite set.  It is set to zero on the
empty set; all substantive lemmas below assume nonemptiness. -/
noncomputable def localAverage (B : Finset G) (f : G → ℝ) : ℝ :=
  (∑ x ∈ B, f x) / B.card

/-- The relative density `|C| / |B|`. -/
noncomputable def relativeDensity (C B : Finset G) : ℝ :=
  C.card / B.card

/-- The normalized `p`-th absolute moment on `B`. -/
noncomputable def localMoment (B : Finset G) (p : ℕ) (f : G → ℝ) : ℝ :=
  localAverage B fun x ↦ |f x| ^ p

/-- Pairing against the normalized indicator of `C`, using the ambient
probability average from `Core`. -/
noncomputable def pairing (f : G → ℝ) (C : Finset G) : ℝ :=
  ambientAverage fun x ↦ f x * normalizedIndicator C x

lemma pairing_eq_localAverage {C : Finset G} (hC : C.Nonempty) (f : G → ℝ) :
    pairing f C = localAverage C f := by
  classical
  unfold pairing localAverage ambientAverage normalizedIndicator indicator
  rw [show (∑ x : G, f x *
      ((Fintype.card G : ℝ) / (C.card : ℝ) * if x ∈ C then 1 else 0)) =
      (Fintype.card G : ℝ) / (C.card : ℝ) * ∑ x ∈ C, f x by
    simp_rw [mul_ite, mul_one, mul_zero]
    simp only [← Finset.sum_filter]
    simp [mul_comm]
    rw [Finset.sum_mul]]
  have hcardC : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
  have hcardG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp

lemma abs_localAverage_le_localAverage_abs {C : Finset G} (f : G → ℝ) :
    |localAverage C f| ≤ localAverage C fun x ↦ |f x| := by
  unfold localAverage
  calc
    |(∑ x ∈ C, f x) / (C.card : ℝ)| =
        |(∑ x ∈ C, f x)| / (C.card : ℝ) := by
      rw [abs_div]
      congr 1
      exact abs_of_nonneg (Nat.cast_nonneg C.card)
    _ ≤ (∑ x ∈ C, |f x|) / (C.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs f C) (by positivity)

/-- Jensen's inequality for the uniform probability measure on a nonempty
finite set, stated with a natural exponent. -/
lemma localAverage_abs_pow_le_localMoment {C : Finset G} (hC : C.Nonempty)
    (p : ℕ) (f : G → ℝ) :
    (localAverage C fun x ↦ |f x|) ^ p ≤ localMoment C p f := by
  let w : G → ℝ := fun _ ↦ (C.card : ℝ)⁻¹
  have hw : ∀ x ∈ C, 0 ≤ w x := by
    intro x hx
    exact inv_nonneg.mpr (by positivity)
  have hws : ∑ x ∈ C, w x = 1 := by
    simp [w, hC.card_ne_zero]
  have hz : ∀ x ∈ C, 0 ≤ |f x| := by
    intro x hx
    positivity
  have h := Real.pow_arith_mean_le_arith_mean_pow C w (fun x ↦ |f x|)
    hw hws hz p
  simpa [localAverage, localMoment, w, div_eq_inv_mul, Finset.mul_sum] using h

/-- Finite Hölder in the precise weighted form needed for lifting from `C` to
the ambient local set `B`.  No roots occur: this is the `p`-th-power form of
`|<f,muWeight_C>| ≤ γ⁻¹ᵖ ‖f‖_{Lᵖ(B)}`. -/
theorem weighted_holder_lifting {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (f : G → ℝ) :
    relativeDensity C B * |pairing f C| ^ p ≤ localMoment B p f := by
  have hB : B.Nonempty := hC.mono hCB
  have hpair : |pairing f C| ^ p ≤ localMoment C p f := by
    rw [pairing_eq_localAverage hC]
    calc
      |localAverage C f| ^ p
          ≤ (localAverage C fun x ↦ |f x|) ^ p :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_localAverage_le_localAverage_abs f) p
      _ ≤ localMoment C p f := localAverage_abs_pow_le_localMoment hC p f
  have hrel : 0 ≤ relativeDensity C B := by
    unfold relativeDensity
    positivity
  calc
    relativeDensity C B * |pairing f C| ^ p
        ≤ relativeDensity C B * localMoment C p f := mul_le_mul_of_nonneg_left hpair hrel
    _ = (∑ x ∈ C, |f x| ^ p) / B.card := by
      unfold relativeDensity localMoment localAverage
      field_simp [hC.card_ne_zero, hB.card_ne_zero]
    _ ≤ (∑ x ∈ B, |f x| ^ p) / B.card := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hCB fun _ _ _ ↦ by positivity
    _ = localMoment B p f := rfl

/-- The abstract localized Hölder dichotomy, with the constants from the
paper.  The approximation hypothesis says that all cross terms contribute at
most one quarter of the requested error.  The density hypothesis is the
root-free form of `γ⁻¹ᵖ ≤ 3/2`. -/
theorem localized_holder_dichotomy {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (_hp : 0 < p) (f : G → ℝ)
    (progression mainTerm ε : ℝ) (hmain : 0 ≤ mainTerm) (hε : 0 ≤ ε)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ ε * mainTerm / 4) :
    |progression - mainTerm| ≤ ε * mainTerm ∨
      (ε * mainTerm / 2) ^ p ≤ localMoment B p f := by
  by_cases hgood : |progression - mainTerm| ≤ ε * mainTerm
  · exact Or.inl hgood
  right
  have htri : |progression - mainTerm| ≤
      |(progression - mainTerm) - pairing f C| + |pairing f C| := by
    calc
      |progression - mainTerm| =
          |((progression - mainTerm) - pairing f C) + pairing f C| := by ring_nf
      _ ≤ |(progression - mainTerm) - pairing f C| + |pairing f C| := abs_add_le _ _
  have hpair : 3 * (ε * mainTerm) / 4 < |pairing f C| := by
    have hlarge : ε * mainTerm < |progression - mainTerm| := lt_of_not_ge hgood
    nlinarith
  have hrel : 0 ≤ relativeDensity C B := by
    unfold relativeDensity
    positivity
  have hpairpow : (3 * (ε * mainTerm) / 4) ^ p ≤ |pairing f C| ^ p :=
    pow_le_pow_left₀ (by positivity) hpair.le p
  have hproduct :
      (2 / 3 : ℝ) ^ p * (3 * (ε * mainTerm) / 4) ^ p ≤
        relativeDensity C B * |pairing f C| ^ p := by
    exact mul_le_mul hdensity hpairpow (by positivity) hrel
  calc
    (ε * mainTerm / 2) ^ p =
        (2 / 3 : ℝ) ^ p * (3 * (ε * mainTerm) / 4) ^ p := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ relativeDensity C B * |pairing f C| ^ p := hproduct
    _ ≤ localMoment B p f := weighted_holder_lifting hC hCB p f

/-- The counting specialization of `localized_holder_dichotomy`.  With error
parameter `1/2`, either the normalized progression count is at least half the
main term or the local `p`-th moment is at least the `p`-th power of one quarter
of the main term. -/
theorem half_main_term_or_quarter_moment {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (hp : 0 < p) (f : G → ℝ)
    (progression mainTerm : ℝ) (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ mainTerm / 8) :
    mainTerm / 2 ≤ progression ∨
      (mainTerm / 4) ^ p ≤ localMoment B p f := by
  have happ : |(progression - mainTerm) - pairing f C| ≤
      (1 / 2 : ℝ) * mainTerm / 4 := by
    convert happrox using 1 <;> ring
  have hdich := localized_holder_dichotomy hC hCB p hp f progression mainTerm
    (1 / 2 : ℝ) hmain.le (by norm_num) hdensity happ
  rcases hdich with hgood | hbad
  · left
    have hlower := (abs_le.mp hgood).1
    linarith
  · right
    convert hbad using 1 <;> ring

/-- Specialized endgame used in progression counting.  Under the balanced
`1/8` moment bound the bad Hölder alternative is impossible, so the normalized
progression count is at least `1/2` of its main term. -/
theorem half_main_term_of_balanced_eighth {B C : Finset G} (hC : C.Nonempty)
    (hCB : C ⊆ B) (p : ℕ) (hp : 0 < p) (f : G → ℝ)
    (progression mainTerm : ℝ) (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ relativeDensity C B)
    (happrox : |(progression - mainTerm) - pairing f C| ≤ mainTerm / 8)
    (hbalanced : localMoment B p f ≤ (mainTerm / 8) ^ p) :
    mainTerm / 2 ≤ progression := by
  rcases half_main_term_or_quarter_moment hC hCB p hp f progression mainTerm hmain
    hdensity happrox with hgood | hbad
  · exact hgood
  · have hpne : p ≠ 0 := Nat.ne_of_gt hp
    have hstrict : (mainTerm / 8) ^ p < (mainTerm / 4) ^ p := by
      apply pow_lt_pow_left₀
      · nlinarith
      · positivity
      · exact hpne
    have : (mainTerm / 4) ^ p ≤ (mainTerm / 8) ^ p := hbad.trans hbalanced
    exact (not_lt_of_ge this hstrict).elim

end HolderLifting

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/GroupCount.lean` -/

section
/-!
# The odd-cyclic progression-counting endpoint

This file performs the normalization-sensitive final counting step in the
Kelley--Meka argument.  If `A'` and `A''` are the translated local endpoint
and middle-term sets, then Holder lifting is applied on the doubled sets

`D = 2 B'` and `C = 2 A''`.

Injectivity of doubling gives `|D| = |B'|`, `|C| = |A''|`, and the exact
probability-normalized convolution identity

`P(A',A'') = |G| * mixedThreeAPCount A' A'' / (|A'|^2 |A''|)`.

The common translation taking `A'` and `A''` back into the original set is
then used to inject the mixed triples into the ordered progressions of that
set.  All constants (`1/2`, `1/8`, and `2/3`) are exposed literally.
-/

open _root_.Finset

namespace GroupCount

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The image of a finite set under doubling. -/
def doubledFinset (S : Finset G) : Finset G :=
  S.image fun x ↦ x + x

@[simp] theorem mem_doubledFinset {S : Finset G} {x : G} :
    x ∈ doubledFinset S ↔ ∃ y ∈ S, y + y = x := by
  simp [doubledFinset]

theorem doubledFinset_nonempty {S : Finset G} (hS : S.Nonempty) :
    (doubledFinset S).Nonempty := by
  exact hS.image _

theorem doubledFinset_mono {S T : Finset G} (hST : S ⊆ T) :
    doubledFinset S ⊆ doubledFinset T := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_doubledFinset.mp hx
  exact mem_doubledFinset.mpr ⟨y, hST hy, rfl⟩

/-- Doubling preserves finite-set cardinality whenever it is injective on the
ambient group. -/
theorem card_doubledFinset (S : Finset G)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    #(doubledFinset S) = #S := by
  exact card_image_of_injective _ hdouble

/-- Consequently doubling preserves relative density. -/
theorem relativeDensity_doubledFinset (S T : Finset G)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    HolderLifting.relativeDensity (doubledFinset S) (doubledFinset T) =
      HolderLifting.relativeDensity S T := by
  simp only [HolderLifting.relativeDensity, card_doubledFinset S hdouble,
    card_doubledFinset T hdouble]

/-! ## The doubled Bohr carrier in an odd cyclic group -/

/-- Transporting Bohr data through an additive equivalence maps its carrier
exactly, not merely up to cardinality. -/
theorem image_bohrCarrier_eq_map
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) :
    B.carrier.image e = (B.map e).carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (BohrData.mem_map_carrier B e y).2 hy
  · intro hx
    refine Finset.mem_image.mpr ⟨e.symm x, ?_, by simp⟩
    have hmap := (BohrData.mem_map_carrier B e (e.symm x)).1
    exact hmap (by simpa using hx)

/-- The transported Bohr datum whose carrier is `2 B`. -/
def doubledBohrData (M : ℕ) (hM : Odd M) (B : BohrData (ZMod M)) :
    BohrData (ZMod M) :=
  B.map (BohrData.zmodDoublingEquiv M hM)

theorem doubledFinset_bohrCarrier_eq_doubledBohrData
    {M : ℕ} [NeZero M] (hM : Odd M) (B : BohrData (ZMod M)) :
    doubledFinset B.carrier = (doubledBohrData M hM B).carrier := by
  rw [doubledFinset, doubledBohrData, ← image_bohrCarrier_eq_map]
  apply Finset.image_congr
  intro x _
  exact BohrData.zmodDoublingEquiv_apply M hM x

@[simp] theorem rank_doubledBohrData
    (M : ℕ) (hM : Odd M) (B : BohrData (ZMod M)) :
    (doubledBohrData M hM B).rank = B.rank := by
  exact BohrData.rank_map B (BohrData.zmodDoublingEquiv M hM)

@[simp] theorem card_doubledBohrData_carrier
    (M : ℕ) [NeZero M] (hM : Odd M) (B : BohrData (ZMod M)) :
    (doubledBohrData M hM B).carrier.card = B.carrier.card := by
  exact BohrData.card_map_zmodDoubling M hM B

/-- The normalized mixed-progression scalar used in Holder lifting.  The
indicators in `FiniteConvolution` have total mass one for counting measure;
the leading ambient cardinality converts the result to the normalized
ambient-measure convention used in the analytic argument. -/
def normalizedMixedProgression (A' A'' : Finset G) : ℝ :=
  (Fintype.card G : ℝ) *
    finiteInner
      (normalizedConvolution (normalizedIndicator A') (normalizedIndicator A'))
      (normalizedIndicator (doubledFinset A''))

/-- Exact normalized-indicator identity, in inverse-cardinality form. -/
theorem normalizedMixedProgression_eq
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    (A' A'' : Finset G) :
    normalizedMixedProgression A' A'' =
      (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) *
        (#A' : ℝ)⁻¹ ^ 2 * (#A'' : ℝ)⁻¹ := by
  rw [normalizedMixedProgression,
    doubledFinset,
    finiteInner_convolution_mixedDoubleIndicator hdouble]
  ring

/-- Exact normalized-indicator identity with a single explicit denominator. -/
theorem normalizedMixedProgression_eq_div
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A' A'' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty) :
    normalizedMixedProgression A' A'' =
      (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) /
        ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) := by
  rw [normalizedMixedProgression_eq hdouble]
  have hA'card : (#A' : ℝ) ≠ 0 := by exact_mod_cast hA'.card_ne_zero
  have hA''card : (#A'' : ℝ) ≠ 0 := by exact_mod_cast hA''.card_ne_zero
  field_simp

/-- The same scalar is the local average over the doubled middle-term set.
This is the precise bridge to `HolderLifting.pairing_eq_localAverage`. -/
theorem normalizedMixedProgression_eq_localAverage
    {A' A'' : Finset G} (hA'' : A''.Nonempty) :
    normalizedMixedProgression A' A'' =
      HolderLifting.localAverage (doubledFinset A'') (fun x ↦
        (Fintype.card G : ℝ) *
          normalizedConvolution (normalizedIndicator A') (normalizedIndicator A') x) := by
  let D := doubledFinset A''
  let F := normalizedConvolution (normalizedIndicator A') (normalizedIndicator A')
  have hD : D.Nonempty := doubledFinset_nonempty hA''
  have hDcard : (#D : ℝ) ≠ 0 := by exact_mod_cast hD.card_ne_zero
  unfold normalizedMixedProgression HolderLifting.localAverage finiteInner
  change (Fintype.card G : ℝ) *
      ∑ x : G, F x * normalizedIndicator D x =
    (∑ x ∈ D, (Fintype.card G : ℝ) * F x) / (#D : ℝ)
  have hrestrict :
      (∑ x : G, F x * normalizedIndicator D x) =
        (∑ x ∈ D, F x) * (#D : ℝ)⁻¹ := by
    change (∑ x : G, F x * (if x ∈ D then (#D : ℝ)⁻¹ else 0)) = _
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter]
    have hfilter : univ.filter (fun x : G ↦ x ∈ D) = D := by ext; simp
    rw [hfilter, Finset.sum_mul]
  rw [hrestrict]
  rw [show (∑ x ∈ D, (Fintype.card G : ℝ) * F x) =
      (Fintype.card G : ℝ) * ∑ x ∈ D, F x by
    rw [Finset.mul_sum]]
  field_simp

/-! ## Conversion from the balanced-restriction norm to the Holder moment -/

/-- The counting-probability normalized indicator is a probability weight in
the sense used by `BalancedRestriction`. -/
theorem normalizedIndicator_isProbabilityWeight {S : Finset G} (hS : S.Nonempty) :
    BalancedRestriction.ProbabilityWeight (normalizedIndicator S) := by
  refine ⟨normalizedIndicator_nonneg S, ?_⟩
  exact sum_normalizedIndicator hS

/-- The weighted absolute moment for the uniform weight on `S` is exactly the
local moment used by Holder lifting. -/
theorem weightedAbsMoment_normalizedIndicator_eq_localMoment
    {S : Finset G} (hS : S.Nonempty) (p : ℕ) (f : G → ℝ) :
    weightedAbsMoment (normalizedIndicator S) f p =
      HolderLifting.localMoment S p f := by
  have hScard : (#S : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  unfold weightedAbsMoment HolderLifting.localMoment HolderLifting.localAverage
    normalizedIndicator
  change (∑ x : G, (if x ∈ S then (#S : ℝ)⁻¹ else 0) * |f x| ^ p) =
    (∑ x ∈ S, |f x| ^ p) / (#S : ℝ)
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter : univ.filter (fun x : G ↦ x ∈ S) = S := by ext; simp
  rw [hfilter]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

/-- A balanced `L^p` bound on the concrete uniform probability measure gives
the power-moment bound expected by `HolderLifting`. -/
theorem localMoment_le_of_weightedLpNorm_le
    {S : Finset G} (hS : S.Nonempty) {p : ℕ} (hp : 0 < p)
    (f : G → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbalanced :
      BalancedRestriction.weightedLpNorm (normalizedIndicator S) f p ≤ C) :
    HolderLifting.localMoment S p f ≤ C ^ p := by
  have hprob := normalizedIndicator_isProbabilityWeight hS
  rw [← weightedAbsMoment_normalizedIndicator_eq_localMoment hS p f,
    ← BalancedRestriction.weightedLpNorm_pow hprob hp]
  exact pow_le_pow_left₀
    (BalancedRestriction.weightedLpNorm_nonneg hprob f p) hbalanced p

/-! ## Concrete terminal data from a located dense pair -/

/-- Generic, fully concrete Holder-count certificate.  The cyclic layer only
has to add its quantitative lower bound for `alpha^3 |B| |B'| / 2`; all set,
translation, doubling, approximation, and balanced-moment data live here. -/
structure HolderCountCertificate (original : Finset G) where
  A' : Finset G
  A'' : Finset G
  B : Finset G
  B' : Finset G
  translate : G
  alpha : ℝ
  p : ℕ
  f : G → ℝ
  A'_nonempty : A'.Nonempty
  A''_nonempty : A''.Nonempty
  B_nonempty : B.Nonempty
  A''_subset_B' : A'' ⊆ B'
  A'_sub_translate : ∀ x ∈ A', x - translate ∈ original
  A''_sub_translate : ∀ x ∈ A'', x - translate ∈ original
  alpha_nonneg : 0 ≤ alpha
  A'_density : alpha * (#B : ℝ) ≤ (#A' : ℝ)
  A''_density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ)
  p_pos : 0 < p
  doubled_density :
    (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B'
  approximation :
    |(normalizedMixedProgression A' A'' -
        (Fintype.card G : ℝ) / (#B : ℝ)) -
        HolderLifting.pairing f (doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#B : ℝ)) / 8
  balanced_moment :
    HolderLifting.localMoment (doubledFinset B') p f ≤
      (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p

/-- The canonical point selected from a terminal simultaneous dense pair. -/
noncomputable def densePairPoint {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : G :=
  Classical.choose h

theorem densePairPoint_density_one {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) :
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childOne.carrier (densePairPoint h) :=
  (Classical.choose_spec h).2.1

theorem densePairPoint_density_two {original : Finset G}
    {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) :
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childTwo.carrier (densePairPoint h) :=
  (Classical.choose_spec h).2.2

/-- The common relative-density lower bound of the two selected fibres. -/
def densePairDensity {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (epsilon : ℝ) : ℝ :=
  (1 - epsilon) * s.density

/-- A half-main-term Holder conclusion gives an exact mixed-count lower
bound. -/
theorem mixedThreeAPCount_lower_bound_of_half
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A' A'' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty)
    {mainTerm : ℝ}
    (hhalf : mainTerm / 2 ≤ normalizedMixedProgression A' A'') :
    mainTerm * (#A' : ℝ) ^ 2 * (#A'' : ℝ) /
        (2 * (Fintype.card G : ℝ)) ≤
      (mixedThreeAPCount A' A'' : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hdenom : (0 : ℝ) < (#A' : ℝ) ^ 2 * (#A'' : ℝ) := by
    positivity
  rw [normalizedMixedProgression_eq_div hdouble hA' hA''] at hhalf
  have hmul :
      mainTerm / 2 * ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) ≤
        (Fintype.card G : ℝ) * (mixedThreeAPCount A' A'' : ℝ) :=
    (le_div_iff₀ hdenom).mp hhalf
  rw [div_le_iff₀ (mul_pos (by norm_num) hG)]
  nlinarith

/-- The complete finite Holder endpoint.  The local set used by Holder is
literally `2 B'`, its dense subset is literally `2 A''`, and the resulting
mixed triples are translated injectively into progressions in `A`. -/
theorem threeAPCount_lower_bound_of_holder
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B' : Finset G} (hA' : A'.Nonempty) (hA'' : A''.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ) {mainTerm : ℝ}
    (hmain : 0 < mainTerm)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' - mainTerm) -
          HolderLifting.pairing f (doubledFinset A'')| ≤ mainTerm / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤ (mainTerm / 8) ^ p) :
    mainTerm * (#A' : ℝ) ^ 2 * (#A'' : ℝ) /
        (2 * (Fintype.card G : ℝ)) ≤ (threeAPCount A : ℝ) := by
  have hC : (doubledFinset A'').Nonempty := doubledFinset_nonempty hA''
  have hCB : doubledFinset A'' ⊆ doubledFinset B' := doubledFinset_mono hA''B'
  have hdensity' :
      (2 / 3 : ℝ) ^ p ≤
        HolderLifting.relativeDensity (doubledFinset A'') (doubledFinset B') := by
    rwa [relativeDensity_doubledFinset A'' B' hdouble]
  have hhalf :
      mainTerm / 2 ≤ normalizedMixedProgression A' A'' :=
    HolderLifting.half_main_term_of_balanced_eighth hC hCB p hp f
      (normalizedMixedProgression A' A'') mainTerm hmain hdensity' happrox hbalanced
  have hmixed :=
    mixedThreeAPCount_lower_bound_of_half hdouble hA' hA'' hhalf
  have hcountNat : mixedThreeAPCount A' A'' ≤ threeAPCount A :=
    mixedThreeAPCount_le_threeAPCount_of_sub_translate t hA'trans hA''trans
  have hcountReal :
      (mixedThreeAPCount A' A'' : ℝ) ≤ (threeAPCount A : ℝ) := by
    exact_mod_cast hcountNat
  exact hmixed.trans hcountReal

/-- Cardinality/density form of the finite Holder endpoint.  If `A'` has
relative density at least `alpha` in `B`, and `A''` has relative density at
least `alpha` in `B'`, then the progression count is at least
`alpha^3 |B| |B'| / 2`. -/
theorem threeAPCount_lower_bound_of_holder_density
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B B' : Finset G}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card G : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p) :
    alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 ≤
      (threeAPCount A : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hBcard : (0 : ℝ) < #B := by exact_mod_cast hB.card_pos
  have hmain : (0 : ℝ) < (Fintype.card G : ℝ) / (#B : ℝ) :=
    div_pos hG hBcard
  have hlower := threeAPCount_lower_bound_of_holder hdouble hA' hA'' hA''B' t
    hA'trans hA''trans hp f hmain hdensity happrox hbalanced
  have hsquare :
      (alpha * (#B : ℝ)) ^ 2 ≤ (#A' : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg halpha hBcard.le) hA'density 2
  have hnumer :
      alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ) ≤
        (#A' : ℝ) ^ 2 * (#A'' : ℝ) := by
    have hmul := mul_le_mul hsquare hA''density
      (mul_nonneg halpha (Nat.cast_nonneg _)) (sq_nonneg (#A' : ℝ))
    nlinarith only [hmul]
  have hleft :
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 =
        (alpha ^ 3 * (#B : ℝ) ^ 2 * (#B' : ℝ)) /
          (2 * (#B : ℝ)) := by
    field_simp
  have hright :
      ((Fintype.card G : ℝ) / (#B : ℝ)) * (#A' : ℝ) ^ 2 *
          (#A'' : ℝ) / (2 * (Fintype.card G : ℝ)) =
        ((#A' : ℝ) ^ 2 * (#A'' : ℝ)) / (2 * (#B : ℝ)) := by
    field_simp
  rw [hright] at hlower
  rw [hleft]
  exact (div_le_div_of_nonneg_right hnumer (by positivity)).trans hlower

namespace HolderCountCertificate

/-- Every concrete Holder certificate gives its advertised mixed-progression
lower bound in the original set. -/
theorem count_bound {original : Finset G} (c : HolderCountCertificate original)
    (hdouble : Function.Injective (fun x : G ↦ x + x)) :
    c.alpha ^ 3 * (#c.B : ℝ) * (#c.B' : ℝ) / 2 ≤
      (threeAPCount original : ℝ) := by
  exact threeAPCount_lower_bound_of_holder_density hdouble
    c.A'_nonempty c.A''_nonempty c.B_nonempty c.A''_subset_B' c.translate
    c.A'_sub_translate c.A''_sub_translate c.alpha_nonneg c.A'_density
    c.A''_density c.p_pos c.f c.doubled_density c.approximation c.balanced_moment

end HolderCountCertificate

/-- A form that can be used directly for the exponential cyclic counting
statement once the balanced-restriction output supplies the final Bohr
cardinality product. -/
theorem cyclic_count_bound_of_holder_density
    (hdouble : Function.Injective (fun x : G ↦ x + x))
    {A A' A'' B B' : Finset G}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : G)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha K : ℝ} {d p : ℕ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    (hp : 0 < p) (f : G → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card G : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card G : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p)
    (hquant : Real.exp (-K * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2) :
    Real.exp (-K * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ^ 2 ≤
      (threeAPCount A : ℝ) := by
  exact hquant.trans <|
    threeAPCount_lower_bound_of_holder_density hdouble hA' hA'' hB hA''B' t
      hA'trans hA''trans halpha hA'density hA''density hp f hdensity happrox hbalanced

/-- Odd cyclic specialization: doubling is supplied by the explicit additive
automorphism from `BohrBasic`. -/
theorem zmod_cyclic_count_bound_of_holder_density
    {M : ℕ} [NeZero M] (hM : Odd M)
    {A A' A'' B B' : Finset (ZMod M)}
    (hA' : A'.Nonempty) (hA'' : A''.Nonempty) (hB : B.Nonempty)
    (hA''B' : A'' ⊆ B') (t : ZMod M)
    (hA'trans : ∀ x ∈ A', x - t ∈ A)
    (hA''trans : ∀ x ∈ A'', x - t ∈ A)
    {alpha K : ℝ} {d p : ℕ} (halpha : 0 ≤ alpha)
    (hA'density : alpha * (#B : ℝ) ≤ (#A' : ℝ))
    (hA''density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ))
    (hp : 0 < p) (f : ZMod M → ℝ)
    (hdensity : (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B')
    (happrox :
      |(normalizedMixedProgression A' A'' -
          (Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) -
          HolderLifting.pairing f (doubledFinset A'')| ≤
        ((Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) / 8)
    (hbalanced :
      HolderLifting.localMoment (doubledFinset B') p f ≤
        (((Fintype.card (ZMod M) : ℝ) / (#B : ℝ)) / 8) ^ p)
    (hquant : Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod M) : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2) :
    Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod M) : ℝ) ^ 2 ≤ (threeAPCount A : ℝ) := by
  apply cyclic_count_bound_of_holder_density
    (BohrData.zmodDoublingEquiv M hM).injective hA' hA'' hB hA''B' t
    hA'trans hA''trans halpha hA'density hA''density hp f hdensity happrox hbalanced
    hquant

end

end GroupCount

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/KelleyMekaCount.lean` -/

section
/-!
# The finite-cyclic Kelley--Meka counting interface

The analytic part of the Kelley--Meka/Bloom--Sisask proof is most naturally
carried out in the odd cyclic group `ZMod (2 * N + 1)`.  This file isolates
the exact quantitative statement required from that argument and proves the
normalization-sensitive passage back to the interval `[1,N]`.

The density parameter is required to be positive.  This is essential: at
parameter zero the putative lower bound would be `N^2`, which already fails
for the full interval when `N >= 2`.
-/

open _root_.Finset
open scoped _root_.NNReal

/-- The group-level output to be supplied by the Bohr-set density iteration.

The ambient group is exactly the no-wrap group `ZMod (2*N+1)`.  Its density
scale uses the group cardinality, not the interval length. -/
def KelleyMekaCyclicCountHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            Real.exp (-K * (d : ℝ) ^ 12) *
                ((intervalModulus N : ℕ) : ℝ) ^ 2 ≤
              (threeAPCount A : ℝ)

/-! ## The actual initial regular-Bohr restriction -/

/-- Empty frequency data presents the whole finite group as a rank-zero Bohr
carrier at every scale.  This is the honest starting datum for the located
restriction iteration. -/
noncomputable def universalBohrData (G : Type*) [AddCommGroup G] : BohrData G where
  freq := ∅
  width := fun _ ↦ 0

@[simp] theorem universalBohrData_rank (G : Type*) [AddCommGroup G] :
    BohrData.rank (universalBohrData G) = 0 := by
  change (∅ : Finset (AddCharacter G)).card = 0
  simp

@[simp] theorem universalBohrData_carrier (G : Type*) [AddCommGroup G] [Fintype G]
    (rho : ℝ≥0) :
    ((universalBohrData G).dilate rho).carrier = (Finset.univ : Finset G) := by
  classical
  ext x
  simp [BohrData.mem_carrier, universalBohrData]

@[simp] theorem universalBohrData_carrier_self
    (G : Type*) [AddCommGroup G] [Fintype G] :
    (universalBohrData G).carrier = (Finset.univ : Finset G) := by
  simpa using universalBohrData_carrier G 1

/-- The initial regular restriction has ambient carrier the whole odd cyclic
group and restricted set exactly `A`. -/
noncomputable def cyclicInitialRestriction (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    BohrStopping.RegularRestriction (ZMod (intervalModulus N)) where
  bohr := universalBohrData (ZMod (intervalModulus N))
  outer := 1
  inner := 1
  regular := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    simp only [universalBohrData_carrier]
    omega
  set := A
  nonempty := hA
  subset_carrier := by
    intro x hx
    rw [universalBohrData_carrier]
    simp

@[simp] theorem cyclicInitialRestriction_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  simp [BohrStopping.RegularRestriction.density,
    BohrStopping.RegularRestriction.ambient, cyclicInitialRestriction]

@[simp] theorem cyclicInitialRestriction_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).rank = 0 := by
  simp [BohrStopping.RegularRestriction.rank, cyclicInitialRestriction]

@[simp] theorem cyclicInitialRestriction_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRestriction N A hA).card = intervalModulus N := by
  simp [BohrStopping.RegularRestriction.card,
    BohrStopping.RegularRestriction.ambient, cyclicInitialRestriction]

/-- The located version of the initial restriction records the identity
translation into the original cyclic set. -/
noncomputable def cyclicInitialLocated (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    DensityStep.LocatedRestriction A where
  restriction := cyclicInitialRestriction N A hA
  shift := 0
  subset_original := by
    intro x hx
    simpa [cyclicInitialRestriction] using hx

@[simp] theorem cyclicInitialLocated_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  exact cyclicInitialRestriction_density N A hA

@[simp] theorem cyclicInitialLocated_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).rank = 0 := by
  exact cyclicInitialRestriction_rank N A hA

@[simp] theorem cyclicInitialLocated_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialLocated N A hA).card = intervalModulus N := by
  exact cyclicInitialRestriction_card N A hA

/-- One thousand twenty-four increments by the fixed factor `1025/1024` pay for
one dyadic density unit.  This is the explicit growth estimate used by the
located maximal chain, with no asymptotic constants hidden. -/
lemma fixedIncrement_growth_of_dyadicScale
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} {d : ℕ}
    (s : DensityStep.LocatedRestriction original)
    (hscale : BohrStopping.OnDyadicScale d s.density) :
    1 < (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) * s.density := by
  have hbase : (2 : ℝ) ≤ (1025 / 1024 : ℝ) ^ 1024 := by
    have h := one_add_mul_le_pow (a := (1 / 1024 : ℝ)) (by norm_num) 1024
    norm_num at h
    exact h
  have hpow : (2 : ℝ) ^ (d + 1) ≤
      (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) := by
    calc
      (2 : ℝ) ^ (d + 1) ≤ ((1025 / 1024 : ℝ) ^ 1024) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) hbase (d + 1)
      _ = (1025 / 1024 : ℝ) ^ (1024 * (d + 1)) := by rw [← pow_mul]
  change 1 / (2 : ℝ) ^ d ≤ s.density at hscale
  have hmul := mul_le_mul hpow hscale (by positivity) (by positivity)
  have hleft : (2 : ℝ) ^ (d + 1) * (1 / (2 : ℝ) ^ d) = 2 := by
    rw [pow_succ]
    field_simp
  rw [hleft] at hmul
  linarith

/-- The concrete terminal certificate produced by balanced restriction and
Hölder lifting.  Every field is an actual finite-set fact; in particular the
two support fields retain the translation back into the original set. -/
structure CyclicHolderCertificate (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (K : ℝ) (d : ℕ) where
  A' : Finset (ZMod (intervalModulus N))
  A'' : Finset (ZMod (intervalModulus N))
  B : Finset (ZMod (intervalModulus N))
  B' : Finset (ZMod (intervalModulus N))
  translate : ZMod (intervalModulus N)
  alpha : ℝ
  p : ℕ
  f : ZMod (intervalModulus N) → ℝ
  A'_nonempty : A'.Nonempty
  A''_nonempty : A''.Nonempty
  B_nonempty : B.Nonempty
  A''_subset_B' : A'' ⊆ B'
  A'_sub_translate : ∀ x ∈ A', x - translate ∈ A
  A''_sub_translate : ∀ x ∈ A'', x - translate ∈ A
  alpha_nonneg : 0 ≤ alpha
  A'_density : alpha * (#B : ℝ) ≤ (#A' : ℝ)
  A''_density : alpha * (#B' : ℝ) ≤ (#A'' : ℝ)
  p_pos : 0 < p
  doubled_density :
    (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B'
  approximation :
    |(GroupCount.normalizedMixedProgression A' A'' -
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) -
        HolderLifting.pairing f (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) / 8
  balanced_moment :
    HolderLifting.localMoment (GroupCount.doubledFinset B') p f ≤
      (((Fintype.card (ZMod (intervalModulus N)) : ℝ) / (#B : ℝ)) / 8) ^ p
  quantitative_size :
    Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2

/-- Raw terminal output expected from the fixed-state analytic argument at a
maximal located restriction.  It records exactly the fibre-density and two
child-cardinality bounds; the global twelfth-power bookkeeping is proved in
this file. -/
structure LocatedHolderTerminalData
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {original : Finset G} (t : DensityStep.LocatedRestriction original)
    (K : ℝ) (d : ℕ) where
  certificate : GroupCount.HolderCountCertificate original
  alpha_lower : (3 / 4 : ℝ) * t.density ≤ certificate.alpha
  B_card : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (t.card : ℝ) ≤ (#certificate.B : ℝ)
  B'_card : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (t.card : ℝ) ≤ (#certificate.B' : ℝ)

namespace CyclicHolderCertificate

private lemma exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-1)).le
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hprod] at hm
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    (by simpa [mul_comm] using hm)

/-- A dyadic density lower bound, after the harmless `3/4` fibre loss,
dominates a uniform twelfth-power exponential. -/
theorem density_cube_bound_of_dyadic
    {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (halpha : (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤ alpha) :
    Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) ≤ alpha ^ 3 / 2 := by
  let m : ℕ := 8 * d ^ 12
  have hexp : Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) =
      Real.exp (-1) ^ m := by
    rw [show -(8 : ℝ) * (d : ℝ) ^ 12 = (m : ℝ) * (-1) by
      simp [m], Real.exp_nat_mul]
  have hhalf : Real.exp (-1) ^ m ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_half m
  have hdPow : d ≤ d ^ 12 := Nat.le_pow (by norm_num)
  have hm : 3 * d + 3 ≤ m := by
    dsimp [m]
    omega
  have hdecay : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (3 * d + 3) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have hcoeff : (1 / 2 : ℝ) ^ (3 * d + 3) ≤
      ((3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d)) ^ 3 / 2 := by
    rw [pow_add, pow_mul]
    ring_nf
    rw [show (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 by norm_num, ← pow_mul]
    gcongr
    all_goals norm_num [Nat.mul_comm]
  calc
    Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) = Real.exp (-1) ^ m := hexp
    _ ≤ (1 / 2 : ℝ) ^ m := hhalf
    _ ≤ (1 / 2 : ℝ) ^ (3 * d + 3) := hdecay
    _ ≤ ((3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d)) ^ 3 / 2 := hcoeff
    _ ≤ alpha ^ 3 / 2 := by gcongr

/-- Add the single global quantitative-size inequality to the generic
located Holder certificate produced by `GroupCount`.  All translation and
normalization-sensitive fields are copied without reinterpretation. -/
def ofHolderCountCertificate {N : ℕ}
    {A : Finset (ZMod (intervalModulus N))} {K : ℝ} {d : ℕ}
    (c : GroupCount.HolderCountCertificate A)
    (hsize : Real.exp (-K * (d : ℝ) ^ 12) *
        (Fintype.card (ZMod (intervalModulus N)) : ℝ) ^ 2 ≤
      c.alpha ^ 3 * (#c.B : ℝ) * (#c.B' : ℝ) / 2) :
    CyclicHolderCertificate N A K d where
  A' := c.A'
  A'' := c.A''
  B := c.B
  B' := c.B'
  translate := c.translate
  alpha := c.alpha
  p := c.p
  f := c.f
  A'_nonempty := c.A'_nonempty
  A''_nonempty := c.A''_nonempty
  B_nonempty := c.B_nonempty
  A''_subset_B' := c.A''_subset_B'
  A'_sub_translate := c.A'_sub_translate
  A''_sub_translate := c.A''_sub_translate
  alpha_nonneg := c.alpha_nonneg
  A'_density := c.A'_density
  A''_density := c.A''_density
  p_pos := c.p_pos
  doubled_density := c.doubled_density
  approximation := c.approximation
  balanced_moment := c.balanced_moment
  quantitative_size := hsize

/-- Two separate Bohr-cardinality losses combine additively in the
exponential constant. -/
theorem bohr_product_of_individual_bounds
    {G : Type*} [Fintype G] {K₁ K₂ : ℝ} {d : ℕ} {B B' : Finset G}
    (hB : Real.exp (-K₁ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ≤
      (#B : ℝ))
    (hB' : Real.exp (-K₂ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ) ≤
      (#B' : ℝ)) :
    Real.exp (-(K₁ + K₂) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤ (#B : ℝ) * (#B' : ℝ) := by
  calc
    Real.exp (-(K₁ + K₂) * (d : ℝ) ^ 12) *
          (Fintype.card G : ℝ) ^ 2 =
        (Real.exp (-K₁ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ)) *
          (Real.exp (-K₂ * (d : ℝ) ^ 12) * (Fintype.card G : ℝ)) := by
      rw [show -(K₁ + K₂) * (d : ℝ) ^ 12 =
          -K₁ * (d : ℝ) ^ 12 + -K₂ * (d : ℝ) ^ 12 by ring,
        Real.exp_add]
      ring
    _ ≤ (#B : ℝ) * (#B' : ℝ) := by
      exact mul_le_mul hB hB' (by positivity) (by positivity)

/-- Multiplication of the density loss and the Bohr-cardinality loss.  This
small lemma keeps the final twelfth-power accounting independent of the
particular constants chosen by the structural theorem. -/
theorem quantitative_size_of_density_and_bohr
    {G : Type*} [Fintype G] {alpha Kdensity Kbohr : ℝ} {d : ℕ}
    {B B' : Finset G}
    (hdensity : Real.exp (-Kdensity * (d : ℝ) ^ 12) ≤ alpha ^ 3 / 2)
    (hbohr : Real.exp (-Kbohr * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤ (#B : ℝ) * (#B' : ℝ)) :
    Real.exp (-(Kdensity + Kbohr) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ^ 2 ≤
      alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 := by
  have hBnonneg : 0 ≤ (#B : ℝ) * (#B' : ℝ) := by positivity
  calc
    Real.exp (-(Kdensity + Kbohr) * (d : ℝ) ^ 12) *
          (Fintype.card G : ℝ) ^ 2 =
        Real.exp (-Kdensity * (d : ℝ) ^ 12) *
          (Real.exp (-Kbohr * (d : ℝ) ^ 12) *
            (Fintype.card G : ℝ) ^ 2) := by
      rw [show -(Kdensity + Kbohr) * (d : ℝ) ^ 12 =
          -Kdensity * (d : ℝ) ^ 12 + -Kbohr * (d : ℝ) ^ 12 by ring,
        Real.exp_add]
      ring
    _ ≤ Real.exp (-Kdensity * (d : ℝ) ^ 12) *
          ((#B : ℝ) * (#B' : ℝ)) :=
      mul_le_mul_of_nonneg_left hbohr (Real.exp_pos _).le
    _ ≤ (alpha ^ 3 / 2) * ((#B : ℝ) * (#B' : ℝ)) :=
      mul_le_mul_of_nonneg_right hdensity hBnonneg
    _ = alpha ^ 3 * (#B : ℝ) * (#B' : ℝ) / 2 := by ring

/-- A terminal certificate gives the desired cyclic progression count. -/
theorem count_bound {N : ℕ} {A : Finset (ZMod (intervalModulus N))}
    {K : ℝ} {d : ℕ} (c : CyclicHolderCertificate N A K d) :
    Real.exp (-K * (d : ℝ) ^ 12) *
        ((intervalModulus N : ℕ) : ℝ) ^ 2 ≤ (threeAPCount A : ℝ) := by
  letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
  have hodd : Odd (intervalModulus N) := by
    exact ⟨N, by simp [intervalModulus, two_mul]⟩
  simpa using GroupCount.zmod_cyclic_count_bound_of_holder_density hodd
    c.A'_nonempty c.A''_nonempty c.B_nonempty c.A''_subset_B' c.translate
    c.A'_sub_translate c.A''_sub_translate c.alpha_nonneg c.A'_density
    c.A''_density c.p_pos c.f c.doubled_density c.approximation
    c.balanced_moment c.quantitative_size

end CyclicHolderCertificate

/-- Exact structural obligation left to the balanced-restriction layer. -/
def KelleyMekaHolderCertificateHypothesis (K : ℝ) : Prop :=
  0 < K ∧
    ∀ (N : ℕ), 1 ≤ N →
      ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
        ∀ d : ℕ, 1 ≤ d →
          Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
              (d : ℝ) * Real.log 2 →
            Nonempty (CyclicHolderCertificate N A K d)

/-- Balanced terminal certificates imply the exact cyclic counting theorem. -/
theorem cyclicCount_of_holderCertificates
    {K : ℝ} (h : KelleyMekaHolderCertificateHypothesis K) :
    KelleyMekaCyclicCountHypothesis K := by
  refine ⟨h.1, ?_⟩
  intro N hN A hA d hd hlog
  exact (Classical.choice (h.2 N hN A hA d hd hlog)).count_bound

private lemma add_one_pow_twelve_le {d : ℕ} (hd : 1 ≤ d) :
    ((d + 1 : ℕ) : ℝ) ^ 12 ≤ (2 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : ((d + 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ) := by
    push_cast
    linarith
  calc
    ((d + 1 : ℕ) : ℝ) ^ 12 ≤ (2 * (d : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hbase 12
    _ = (2 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by rw [mul_pow]

namespace CyclicHolderCertificate

/-- One final child-cardinality loss, following at most `1024(d+1)` located
increments with the same eleventh-power step cost, is absorbed by the
twelfth-power constant `1025 * 2^12 * K`. -/
theorem child_card_bound_of_located_chain
    {G : Type*} [Fintype G] {K : ℝ} (hK : 0 ≤ K)
    {d n terminalCard : ℕ} (hd : 1 ≤ d) (hn : n ≤ 1024 * (d + 1))
    {B : Finset G}
    (hchain : Real.exp (-(n : ℝ) *
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)) * (Fintype.card G : ℝ) ≤
        (terminalCard : ℝ))
    (hchild : Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (terminalCard : ℝ) ≤ (#B : ℝ)) :
    Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
        (Fintype.card G : ℝ) ≤ (#B : ℝ) := by
  let step : ℝ := K * ((d + 1 : ℕ) : ℝ) ^ 11
  have hn' : n + 1 ≤ 1025 * (d + 1) := by omega
  have hnR : (n : ℝ) + 1 ≤ 1025 * ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast hn'
  have hstep : 0 ≤ step := by
    dsimp [step]
    positivity
  have hcostOne : ((n : ℝ) + 1) * step ≤
      1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := by
    calc
      ((n : ℝ) + 1) * step ≤
          (1025 * ((d + 1 : ℕ) : ℝ)) * step :=
        mul_le_mul_of_nonneg_right hnR hstep
      _ = 1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := by
        simp only [step]
        ring
  have hpow := add_one_pow_twelve_le hd
  have hcost : ((n : ℝ) + 1) * step ≤
      (1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by
    calc
      ((n : ℝ) + 1) * step ≤
          1025 * K * ((d + 1 : ℕ) : ℝ) ^ 12 := hcostOne
      _ ≤ 1025 * K * ((2 : ℝ) ^ 12 * (d : ℝ) ^ 12) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hK)
      _ = (1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12 := by ring
  have hcombined : Real.exp (-((n : ℝ) + 1) * step) *
      (Fintype.card G : ℝ) ≤ (#B : ℝ) := by
    calc
      Real.exp (-((n : ℝ) + 1) * step) * (Fintype.card G : ℝ) =
          Real.exp (-step) *
            (Real.exp (-(n : ℝ) * step) * (Fintype.card G : ℝ)) := by
        rw [show -((n : ℝ) + 1) * step =
            -step + (-(n : ℝ) * step) by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-step) * (terminalCard : ℝ) :=
        mul_le_mul_of_nonneg_left (by simpa [step] using hchain)
          (Real.exp_pos _).le
      _ ≤ (#B : ℝ) := by simpa [step] using hchild
  have hexp : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) ≤
      Real.exp (-((n : ℝ) + 1) * step) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hcombined

/-- Assemble a raw analytic terminal certificate with the actual located
chain.  The output constant is explicit: `8` pays for density, while the two
child carriers each pay `257 * 2^12 * K`. -/
noncomputable def of_locatedTerminalData
    {N d n : ℕ} (hd : 1 ≤ d)
    {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    {K : ℝ} (hK : 0 ≤ K)
    {t : DensityStep.LocatedRestriction A}
    (hn : n ≤ 1024 * (d + 1))
    (hdyadic : BohrStopping.OnDyadicScale d
      (cyclicInitialLocated N A hA).density)
    (hdensity : (1025 / 1024 : ℝ) ^ n *
        (cyclicInitialLocated N A hA).density ≤ t.density)
    (hcard : Real.exp (-(n : ℝ) *
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        ((cyclicInitialLocated N A hA).card : ℝ) ≤ (t.card : ℝ))
    (terminal : LocatedHolderTerminalData t K d) :
    CyclicHolderCertificate N A
      (8 + 2050 * (2 : ℝ) ^ 12 * K) d := by
  letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
  let c := terminal.certificate
  have hinitNonneg : 0 ≤ (cyclicInitialLocated N A hA).density :=
    (cyclicInitialLocated N A hA).density_pos.le
  have hqpow : (1 : ℝ) ≤ (1025 / 1024 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num)
  have hinit_le : (cyclicInitialLocated N A hA).density ≤ t.density := by
    calc
      (cyclicInitialLocated N A hA).density =
          1 * (cyclicInitialLocated N A hA).density := by ring
      _ ≤ (1025 / 1024 : ℝ) ^ n * (cyclicInitialLocated N A hA).density :=
        mul_le_mul_of_nonneg_right hqpow hinitNonneg
      _ ≤ t.density := hdensity
  have hscale : (1 / (2 : ℝ) ^ d) ≤
      (cyclicInitialLocated N A hA).density := hdyadic
  have halpha : (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤ c.alpha := by
    calc
      (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ d) ≤
          (3 / 4 : ℝ) * (cyclicInitialLocated N A hA).density :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ ≤ (3 / 4 : ℝ) * t.density :=
        mul_le_mul_of_nonneg_left hinit_le (by norm_num)
      _ ≤ c.alpha := terminal.alpha_lower
  have hdensityCube : Real.exp (-(8 : ℝ) * (d : ℝ) ^ 12) ≤
      c.alpha ^ 3 / 2 := density_cube_bound_of_dyadic hd halpha
  have hchainCard : Real.exp (-(n : ℝ) *
        (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (t.card : ℝ) := by
    simpa only [cyclicInitialLocated_card, ZMod.card] using hcard
  have hB : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (#c.B : ℝ) := by
    exact child_card_bound_of_located_chain
      (G := ZMod (intervalModulus N)) (K := K) hK
      (d := d) (n := n) (terminalCard := t.card) hd hn hchainCard terminal.B_card
  have hB' : Real.exp (-(1025 * (2 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) *
      (Fintype.card (ZMod (intervalModulus N)) : ℝ) ≤ (#c.B' : ℝ) := by
    exact child_card_bound_of_located_chain
      (G := ZMod (intervalModulus N)) (K := K) hK
      (d := d) (n := n) (terminalCard := t.card) hd hn hchainCard terminal.B'_card
  have hbohr := bohr_product_of_individual_bounds hB hB'
  have hsize := quantitative_size_of_density_and_bohr hdensityCube hbohr
  exact ofHolderCountCertificate c (by
    convert hsize using 1 <;> ring)

end CyclicHolderCertificate

private lemma intervalModulus_cast_le_four_mul {N : ℕ} (hN : 1 ≤ N) :
    (((intervalModulus N : ℕ) : ℝ)) ≤ 4 * (N : ℝ) := by
  push_cast
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

private lemma log_intervalModulus_div_card_le
    {N d : ℕ} {A : Finset ℕ} (hN : 1 ≤ N) (hA : A.Nonempty)
    (hlog : Real.log ((N : ℝ) / (#A : ℝ)) ≤ (d : ℝ) * Real.log 2) :
    Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hAreal : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hratioN : (0 : ℝ) < (N : ℝ) / (#A : ℝ) := div_pos hNreal hAreal
  have hratio_le :
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        4 * ((N : ℝ) / (#A : ℝ)) := by
    calc
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
          (4 * (N : ℝ)) / (#A : ℝ) :=
        div_le_div_of_nonneg_right (intervalModulus_cast_le_four_mul hN) hAreal.le
      _ = 4 * ((N : ℝ) / (#A : ℝ)) := by ring
  calc
    Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        Real.log (4 * ((N : ℝ) / (#A : ℝ))) :=
      Real.log_le_log (by positivity) hratio_le
    _ = 2 * Real.log 2 + Real.log ((N : ℝ) / (#A : ℝ)) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hratioN.ne',
        show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    _ ≤ 2 * Real.log 2 + (d : ℝ) * Real.log 2 := by linarith
    _ = ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      ring

private lemma add_two_pow_twelve_le {d : ℕ} (hd : 1 ≤ d) :
    ((d + 2 : ℕ) : ℝ) ^ 12 ≤ (3 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbase : ((d + 2 : ℕ) : ℝ) ≤ 3 * (d : ℝ) := by
    push_cast
    linarith
  calc
    ((d + 2 : ℕ) : ℝ) ^ 12 ≤ (3 * (d : ℝ)) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hbase 12
    _ = (3 : ℝ) ^ 12 * (d : ℝ) ^ 12 := by rw [mul_pow]

/-- The cyclic Kelley--Meka estimate implies the interval estimate.  The
harmless factor `3^12` absorbs both the change from `N` to `2*N+1` and the
two extra dyadic density units (`2*N+1 <= 4*N`). -/
theorem orderedCount_of_cyclic
    {K : ℝ} (hcyclic : KelleyMekaCyclicCountHypothesis K) :
    KelleyMekaOrderedCountHypothesis ((3 : ℝ) ^ 12 * K) 1 := by
  refine ⟨mul_pos (pow_pos (by norm_num) _) hcyclic.1, ?_⟩
  intro N hN A hAIcc hA d hd hlog
  have hAle : ∀ a ∈ A, a ≤ N := by
    intro a ha
    exact (Finset.mem_Icc.mp (hAIcc ha)).2
  have hImageNonempty : (intervalImage N A).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨intervalEmbedding N a, mem_intervalImage.mpr ⟨a, ha, rfl⟩⟩
  have hImageCard : #(intervalImage N A) = #A := card_intervalImage hAle
  have hgroupLog :
      Real.log (((intervalModulus N : ℕ) : ℝ) /
          (#(intervalImage N A) : ℝ)) ≤
        ((d + 2 : ℕ) : ℝ) * Real.log 2 := by
    rw [hImageCard]
    exact log_intervalModulus_div_card_le hN hA hlog
  have hgroup := hcyclic.2 N hN (intervalImage N A) hImageNonempty
    (d + 2) (by omega) hgroupLog
  have hpow := add_two_pow_twelve_le hd
  have hexp :
      Real.exp (-((3 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) ≤
        Real.exp (-K * ((d + 2 : ℕ) : ℝ) ^ 12) := by
    apply Real.exp_le_exp.mpr
    have hK := hcyclic.1.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hK]
  have hNcard : (N : ℝ) ^ 2 ≤ (((intervalModulus N : ℕ) : ℝ)) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    push_cast
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith
  calc
    Real.exp (-((3 : ℝ) ^ 12 * K) * (d : ℝ) ^ 12) * (N : ℝ) ^ 2 ≤
        Real.exp (-K * ((d + 2 : ℕ) : ℝ) ^ 12) *
          (((intervalModulus N : ℕ) : ℝ)) ^ 2 :=
      mul_le_mul hexp hNcard (sq_nonneg _) (Real.exp_pos _).le
    _ ≤ (threeAPCount (intervalImage N A) : ℝ) := hgroup
    _ = (threeAPCount A : ℝ) := by rw [threeAPCount_intervalImage hAle]

/-- Existential form of `orderedCount_of_cyclic`, used by the public theorem.
The only remaining input after this lemma is the unconditional cyclic-group
counting theorem supplied by the analytic density iteration. -/
theorem exists_orderedCount_of_exists_cyclic
    (h : ∃ K : ℝ, KelleyMekaCyclicCountHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact ⟨(3 : ℝ) ^ 12 * K, 1, orderedCount_of_cyclic hK⟩

/-- Full assembly from concrete balanced/Hölder certificates to the ordered
interval hypothesis. -/
theorem exists_orderedCount_of_exists_holderCertificates
    (h : ∃ K : ℝ, KelleyMekaHolderCertificateHypothesis K) :
    ∃ K : ℝ, ∃ N₀ : ℕ, KelleyMekaOrderedCountHypothesis K N₀ := by
  obtain ⟨K, hK⟩ := h
  exact exists_orderedCount_of_exists_cyclic
    ⟨K, cyclicCount_of_holderCertificates hK⟩

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/LpOrthogonality.lean` -/

section
/-!
# Even-moment Fourier orthogonality

This file isolates the phase-removal argument used in the balanced-restriction
step for Erdős Problem 140.  All averages are normalized Fintype expectations.
For a positive even natural number `p` we prove that the `p`-th moment of
`f * f` is at most the corresponding moment of `f ○ f`.  We also record the
weighted, translated version: translation contributes only a unit-modulus
character, while a spectrally nonnegative weight contributes nonnegative
Fourier coefficients, so the same triangle-inequality argument applies.
-/

noncomputable section

open _root_.AddChar _root_.Finset Fintype _root_.Function _root_.RCLike
open scoped BigOperators ComplexConjugate

namespace LpOrthogonality

open FiniteFourier

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The normalized absolute `p`-th moment on a finite type. -/
def absMoment (f : G → ℂ) (p : ℕ) : ℝ :=
  𝔼 x : G, ‖f x‖ ^ p

/-- A normalized absolute moment with a real physical-space weight. -/
def weightedAbsMoment (nu : G → ℝ) (f : G → ℂ) (p : ℕ) : ℝ :=
  𝔼 x : G, nu x * ‖f x‖ ^ p

/-- Natural-exponent weighted `L^p` norm. -/
def weightedLpNorm (nu : G → ℝ) (f : G → ℂ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (weightedAbsMoment nu f p) ^ (1 / (p : ℝ))

/-- The Fourier character average of a real weight.  This is the Fourier
coefficient at the inverse character; using this convention makes translation
by `t` contribute the factor `chi t` below. -/
def characterAverage (nu : G → ℝ) (chi : AddChar G ℂ) : ℂ :=
  𝔼 x : G, (nu x : ℂ) * chi x

/-- A real weight is spectrally nonnegative when all its character averages
are nonnegative real numbers.  Equivalently, all of its normalized Fourier
coefficients are nonnegative (inversion of the character only permutes the
dual group). -/
def SpectrallyNonnegative (nu : G → ℝ) : Prop :=
  ∀ chi : AddChar G ℂ,
    0 ≤ (characterAverage nu chi).re ∧ (characterAverage nu chi).im = 0

lemma ofReal_countingConvolution (a b : G → ℝ) (x : G) :
    (Erdos140.normalizedConvolution a b x : ℂ) =
      (Fintype.card G : ℂ) *
        FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ b) x := by
  unfold Erdos140.normalizedConvolution FiniteFourier.convolution
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  field_simp
  simp [Function.comp_apply]

lemma ofReal_countingAutocorrelation (a : G → ℝ) (x : G) :
    (Erdos140.normalizedDifferenceConvolution a a x : ℂ) =
      (Fintype.card G : ℂ) *
        differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x := by
  unfold Erdos140.normalizedDifferenceConvolution FiniteFourier.differenceConvolution
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  field_simp
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ ?_
  simp

lemma characterAverage_eq_ofReal {nu : G → ℝ}
    (hnu : SpectrallyNonnegative nu) (chi : AddChar G ℂ) :
    characterAverage nu chi = ((characterAverage nu chi).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (hnu chi).2

lemma characterAverage_translate (nu : G → ℝ) (chi : AddChar G ℂ) (t : G) :
    (𝔼 x : G, (nu (x - t) : ℂ) * chi x) = chi t * characterAverage nu chi := by
  unfold characterAverage
  rw [mul_expect]
  refine Fintype.expect_equiv (M := ℂ) (Equiv.subRight t : G ≃ G) _ _ fun y ↦ ?_
  simp only [Equiv.subRight_apply, sub_eq_add_neg]
  have hc : chi y = chi t * chi (y + -t) := by
    rw [← map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring

lemma norm_characterAverage_translate {nu : G → ℝ}
    (hnu : SpectrallyNonnegative nu) (chi : AddChar G ℂ) (t : G) :
    ‖𝔼 x : G, (nu (x - t) : ℂ) * chi x‖ = (characterAverage nu chi).re := by
  rw [characterAverage_translate, norm_mul, AddChar.norm_apply,
    one_mul, characterAverage_eq_ofReal hnu]
  simp [abs_of_nonneg (hnu chi).1]

/-- A counting convolution of two counting autocorrelations has nonnegative
spectrum.  Its normalized Fourier model carries the exact factor `|G|^3`. -/
theorem spectrallyNonnegative_counting_autocorrelation_convolution
    (a b : G → ℝ) :
    SpectrallyNonnegative
      (Erdos140.normalizedConvolution
        (Erdos140.normalizedDifferenceConvolution a a)
        (Erdos140.normalizedDifferenceConvolution b b)) := by
  let ac : G → ℂ := (↑) ∘ a
  let bc : G → ℂ := (↑) ∘ b
  let da : G → ℂ := differenceConvolution ac ac
  let db : G → ℂ := differenceConvolution bc bc
  let h : G → ℂ := FiniteFourier.convolution da db
  have hweight (x : G) :
      (Erdos140.normalizedConvolution
          (Erdos140.normalizedDifferenceConvolution a a)
          (Erdos140.normalizedDifferenceConvolution b b) x : ℂ) =
        (Fintype.card G : ℂ) ^ 3 * h x := by
    rw [ofReal_countingConvolution]
    have hua : ((↑) ∘ Erdos140.normalizedDifferenceConvolution a a) =
        fun y ↦ (Fintype.card G : ℂ) * da y := by
      funext y
      exact ofReal_countingAutocorrelation a y
    have hub : ((↑) ∘ Erdos140.normalizedDifferenceConvolution b b) =
        fun y ↦ (Fintype.card G : ℂ) * db y := by
      funext y
      exact ofReal_countingAutocorrelation b y
    rw [hua, hub]
    simp only [h, da, db, FiniteFourier.convolution,
      Fintype.expect_eq_sum_div_card]
    have hcard : (Fintype.card G : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  intro chi
  have havg :
      characterAverage
          (Erdos140.normalizedConvolution
            (Erdos140.normalizedDifferenceConvolution a a)
            (Erdos140.normalizedDifferenceConvolution b b)) chi =
        (Fintype.card G : ℂ) ^ 3 * coeff h (-chi) := by
    unfold characterAverage
    simp_rw [hweight]
    calc
      (𝔼 x : G, (Fintype.card G : ℂ) ^ 3 * h x * chi x) =
          (Fintype.card G : ℂ) ^ 3 * (𝔼 x : G, h x * chi x) := by
        calc
          _ = 𝔼 x : G, (Fintype.card G : ℂ) ^ 3 * (h x * chi x) := by
            congr 1 with x
            ring
          _ = _ := by rw [← mul_expect]
      _ = _ := by
        congr 1
        simp [coeff, wInner_cWeight_eq_expect, inner_apply, map_neg_eq_conj]
  have hreal :
      characterAverage
          (Erdos140.normalizedConvolution
            (Erdos140.normalizedDifferenceConvolution a a)
            (Erdos140.normalizedDifferenceConvolution b b)) chi =
        (((Fintype.card G : ℝ) ^ 3 * Complex.normSq (coeff ac (-chi)) *
          Complex.normSq (coeff bc (-chi)) : ℝ) : ℂ) := by
    rw [havg]
    simp only [h, coeff_convolution, da, db, coeff_autocorrelation]
    push_cast
    ring
  rw [hreal]
  constructor
  · simpa only [Complex.ofReal_re] using
      (mul_nonneg
      (mul_nonneg (by positivity) (Complex.normSq_nonneg _))
      (Complex.normSq_nonneg _))
  · exact Complex.ofReal_im _

lemma absMoment_nonneg (f : G → ℂ) (p : ℕ) : 0 ≤ absMoment f p := by
  exact expect_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _

/-- The natural-exponent normalized `L^p` norm.  Exponent zero is assigned
zero; all substantive results below assume the exponent is positive. -/
def lpNorm (f : G → ℂ) (p : ℕ) : ℝ :=
  if p = 0 then 0 else (absMoment f p) ^ (1 / (p : ℝ))

lemma lpNorm_nonneg (f : G → ℂ) (p : ℕ) : 0 ≤ lpNorm f p := by
  unfold lpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (absMoment_nonneg f p) _

/-- Expansion of an even normalized moment of a finite Fourier polynomial.
The two tuples index the `k` conjugated and `k` unconjugated factors. -/
lemma absMoment_two_mul_sum_pow {I : Type*} {k : ℕ} (hk : k ≠ 0)
    (s : Finset I) (u : I → G → ℂ) :
    (absMoment (∑ i ∈ s, u i) (2 * k) : ℂ) =
      ∑ x ∈ s ^^ k, ∑ y ∈ s ^^ k,
        𝔼 a : G, (∏ i, conj (u (x i) a)) * ∏ i, u (y i) a := by
  rw [absMoment]
  push_cast
  simp_rw [Finset.sum_apply]
  calc
    (𝔼 a : G, (‖∑ i ∈ s, u i a‖ : ℂ) ^ (2 * k)) =
        𝔼 a : G, (∑ i ∈ s, conj (u i a)) ^ k *
          (∑ j ∈ s, u j a) ^ k := by
      congr 1 with a
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by
      simp_rw [sum_pow', Finset.sum_mul_sum, expect_sum_comm]

/-- Weighted version of `absMoment_two_mul_sum_pow`. -/
lemma weightedAbsMoment_two_mul_sum_pow {I : Type*} {k : ℕ} (_hk : k ≠ 0)
    (nu : G → ℝ) (s : Finset I) (u : I → G → ℂ) :
    (weightedAbsMoment nu (∑ i ∈ s, u i) (2 * k) : ℂ) =
      ∑ x ∈ s ^^ k, ∑ y ∈ s ^^ k,
        𝔼 a : G, (nu a : ℂ) *
          ((∏ i, conj (u (x i) a)) * ∏ i, u (y i) a) := by
  rw [weightedAbsMoment]
  push_cast
  simp_rw [Finset.sum_apply]
  calc
    (𝔼 a : G, (nu a : ℂ) * (‖∑ i ∈ s, u i a‖ : ℂ) ^ (2 * k)) =
        𝔼 a : G, (nu a : ℂ) *
          ((∑ i ∈ s, conj (u i a)) ^ k * (∑ j ∈ s, u j a) ^ k) := by
      congr 1 with a
      simp_rw [pow_mul, ← Complex.conj_mul', mul_pow, map_sum]
    _ = _ := by
      simp_rw [sum_pow', Finset.sum_mul_sum, mul_sum, expect_sum_comm]

lemma weightedAbsMoment_nonneg {nu : G → ℝ} (hnu : ∀ x, 0 ≤ nu x)
    (f : G → ℂ) (p : ℕ) : 0 ≤ weightedAbsMoment nu f p := by
  exact expect_nonneg fun x _ ↦ mul_nonneg (hnu x) (pow_nonneg (norm_nonneg _) _)

lemma weightedLpNorm_of_pos (nu : G → ℝ) (f : G → ℂ) {p : ℕ} (hp : 0 < p) :
    weightedLpNorm nu f p = (weightedAbsMoment nu f p) ^ (1 / (p : ℝ)) := by
  simp [weightedLpNorm, hp.ne']

lemma weightedLpNorm_nonneg {nu : G → ℝ} (hnu : ∀ x, 0 ≤ nu x)
    (f : G → ℂ) (p : ℕ) : 0 ≤ weightedLpNorm nu f p := by
  unfold weightedLpNorm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (weightedAbsMoment_nonneg hnu f p) _

/-- Translated positive-definite-measure comparison. -/
theorem weightedAbsMoment_translate_convolution_le_autocorrelation
    {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (nu : G → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (hspec : SpectrallyNonnegative nu) (t : G) (f : G → ℂ) :
    weightedAbsMoment (fun x ↦ nu (x - t)) (convolution f f) p ≤
      weightedAbsMoment nu (differenceConvolution f f) p := by
  obtain ⟨k, rfl⟩ := heven.two_dvd
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hp
  let term : (Fin k → AddChar G ℂ) × (Fin k → AddChar G ℂ) → ℂ :=
    fun psi ↦
      conj (∏ i, coeff f (psi.1 i) ^ 2) *
        (∏ i, coeff f (psi.2 i) ^ 2) *
          (𝔼 x : G, (nu (x - t) : ℂ) *
            ((∑ i, psi.2 i - ∑ i, psi.1 i) x))
  refine Complex.le_of_eq_sum_of_eq_sum_norm term univ
    (weightedAbsMoment_nonneg (fun x ↦ hnu (x - t)) _ _) ?_ ?_
  · have hinv : convolution f f =
        ∑ chi : AddChar G ℂ, fun x ↦ coeff (convolution f f) chi * chi x := by
      funext x
      simpa only [Finset.sum_apply] using (inversion (convolution f f) x).symm
    rw [hinv]
    have hm := weightedAbsMoment_two_mul_sum_pow (G := G) hp
      (fun x ↦ nu (x - t)) (univ : Finset (AddChar G ℂ))
      (fun chi x ↦ coeff (convolution f f) chi * chi x)
    rw [hm]
    simp only [term]
    simp_rw [coeff_convolution, ← sq, Fintype.sum_prod_type, mul_expect,
      AddChar.sub_apply]
    simp [term, mul_mul_mul_comm, mul_comm, map_neg_eq_conj, prod_mul_distrib]
    ring
  · have hinv : differenceConvolution f f =
        ∑ chi : AddChar G ℂ,
          fun x ↦ coeff (differenceConvolution f f) chi * chi x := by
      funext x
      simpa only [Finset.sum_apply] using
        (inversion (differenceConvolution f f) x).symm
    rw [hinv]
    have hm := weightedAbsMoment_two_mul_sum_pow (G := G) hp nu
      (univ : Finset (AddChar G ℂ))
      (fun chi x ↦ coeff (differenceConvolution f f) chi * chi x)
    rw [hm]
    simp only [term]
    simp_rw [coeff_differenceConvolution, Complex.mul_conj',
      Fintype.sum_prod_type, mul_expect]
    congr 1 with psi
    congr 1 with phi
    simp only [map_mul, map_pow, prod_mul_distrib, mul_mul_mul_comm,
      ← mul_expect, map_prod, AddChar.sub_apply, AddChar.coe_sum,
      Finset.prod_apply, norm_mul, norm_prod, norm_pow, RCLike.norm_conj,
      Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_pow,
      Complex.conj_ofReal]
    have hchars :
        (𝔼 x : G, (nu x : ℂ) *
            ((∏ i, conj (psi i x)) * ∏ i, phi i x)) =
          characterAverage nu (∑ i, phi i - ∑ i, psi i) := by
      simp [characterAverage, map_neg_eq_conj, mul_comm, mul_left_comm,
        AddChar.sub_apply]
    let a : ℂ :=
      (∏ i, (‖coeff f (psi i)‖ ^ 2 : ℂ)) *
        ∏ i, (‖coeff f (phi i)‖ ^ 2 : ℂ)
    let c : ℂ :=
      conj (∏ i, coeff f (psi i) ^ 2) * ∏ i, coeff f (phi i) ^ 2
    let eta : AddChar G ℂ := ∑ i, phi i - ∑ i, psi i
    have hleft :
        (𝔼 x : G, (nu x : ℂ) *
            (a * ((∏ i, conj (psi i x)) * ∏ i, phi i x))) =
          a * characterAverage nu eta := by
      calc
        _ = 𝔼 x : G, a * ((nu x : ℂ) *
              ((∏ i, conj (psi i x)) * ∏ i, phi i x)) := by
            congr 1 with x
            ring
        _ = a * (𝔼 x : G, (nu x : ℂ) *
              ((∏ i, conj (psi i x)) * ∏ i, phi i x)) := by
            rw [← mul_expect]
        _ = _ := by simpa only [eta] using congrArg (a * ·) hchars
    have hinside :
        (𝔼 x : G, c * (nu (x - t) : ℂ) *
            ((∏ i, phi i x) * ∏ i, psi i (-x))) =
          c * (𝔼 x : G, (nu (x - t) : ℂ) * eta x) := by
      calc
        _ = 𝔼 x : G, c * ((nu (x - t) : ℂ) * eta x) := by
          congr 1 with x
          dsimp only [eta]
          simp [map_neg_eq_conj, AddChar.sub_apply, mul_comm, mul_left_comm]
          ring
        _ = _ := by rw [← mul_expect]
    have hgoal :
        (𝔼 x : G, (nu x : ℂ) *
            (a * ((∏ i, conj (psi i x)) * ∏ i, phi i x))) =
          (‖𝔼 x : G, c * (nu (x - t) : ℂ) *
            ((∏ i, phi i x) * ∏ i, psi i (-x))‖ : ℂ) := by
      rw [hleft, hinside, norm_mul,
        norm_characterAverage_translate hspec eta t]
      rw [characterAverage_eq_ofReal hspec]
      dsimp only [a, c]
      push_cast
      simp [abs_of_nonneg (hspec eta).1, norm_prod]
    simpa [a, c, pow_two, prod_mul_distrib, mul_assoc, mul_comm, mul_left_comm] using hgoal

/-- The translated comparison with unnormalized finite sums. -/
theorem sum_translate_convolution_le_autocorrelation
    {p : ℕ} (hp : p ≠ 0) (heven : Even p)
    (nu : G → ℝ) (hnu : ∀ x, 0 ≤ nu x)
    (hspec : SpectrallyNonnegative nu) (t : G) (f : G → ℂ) :
    ∑ x : G, nu (x - t) * ‖convolution f f x‖ ^ p ≤
      ∑ x : G, nu x * ‖differenceConvolution f f x‖ ^ p := by
  have h := weightedAbsMoment_translate_convolution_le_autocorrelation
    hp heven nu hnu hspec t f
  simp only [weightedAbsMoment, Fintype.expect_eq_sum_div_card] at h
  exact (div_le_div_iff_of_pos_right
    (by positivity : (0 : ℝ) < Fintype.card G)).mp h

end LpOrthogonality

end
end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/ConvolutionComparison.lean` -/

section
/-!
# Convolution versus autocorrelation on a narrow Bohr weight

This file assembles the two ingredients in the Kelley--Meka/Bloom--Sisask
convolution comparison: factor-two Bohr majorization and phase removal at an
even exponent.  The small-set hypothesis is quantitative: both smoothing
sets lie in `B_(eta)`, and coarse regularity is assumed on the full fourfold
shell `B_(rho ± 4 eta)`.
-/

open _root_.Finset Fintype _root_.Function
open scoped BigOperators _root_.NNReal

namespace ConvolutionComparison

noncomputable section

open FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The spectrally nonnegative comparison weight
`(muWeight_C ○ muWeight_C) * (muWeight_D ○ muWeight_D)`, in counting-measure
normalization. -/
def comparisonWeight (C D : Finset G) : G → ℝ :=
  normalizedConvolution
    (normalizedDifferenceConvolution (normalizedIndicator C) (normalizedIndicator C))
    (normalizedDifferenceConvolution (normalizedIndicator D) (normalizedIndicator D))

theorem comparisonWeight_nonneg (C D : Finset G) (x : G) :
    0 ≤ comparisonWeight C D x := by
  apply normalizedConvolution_nonneg
  · exact normalizedDifferenceConvolution_nonneg
      (normalizedIndicator_nonneg C) (normalizedIndicator_nonneg C)
  · exact normalizedDifferenceConvolution_nonneg
      (normalizedIndicator_nonneg D) (normalizedIndicator_nonneg D)

theorem sum_comparisonWeight {C D : Finset G}
    (hC : C.Nonempty) (hD : D.Nonempty) :
    ∑ x : G, comparisonWeight C D x = 1 := by
  rw [comparisonWeight, sum_normalizedConvolution,
    sum_normalizedDifferenceConvolution, sum_normalizedDifferenceConvolution,
    sum_normalizedIndicator hC, sum_normalizedIndicator hD]
  norm_num

/-- An autocorrelation of a measure supported in `B_eta` is supported in
`B_(2 eta)`. -/
theorem differenceIndicator_support_two_mul
    {B : BohrData G} {eta : ℝ≥0} {C : Finset G}
    (hC : C.Nonempty) (hCsmall : C ⊆ (B.dilate eta).carrier)
    {x : G}
    (hx : normalizedDifferenceConvolution
      (normalizedIndicator C) (normalizedIndicator C) x ≠ 0) :
    x ∈ (B.dilate (2 * eta)).carrier := by
  by_contra hxout
  apply hx
  rw [normalizedDifferenceConvolution]
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : normalizedIndicator C y = 0
  · simp [hy]
  have hyC : y ∈ C := (normalizedIndicator_ne_zero_iff hC y).mp hy
  by_cases hyx : normalizedIndicator C (y - x) = 0
  · simp [hyx]
  have hyxC : y - x ∈ C :=
    (normalizedIndicator_ne_zero_iff hC (y - x)).mp hyx
  have hmem := BohrData.sub_mem_dilate (hCsmall hyC) (hCsmall hyxC)
  have heq : y - (y - x) = x := by abel
  rw [heq] at hmem
  exact (hxout (by simpa [two_mul] using hmem)).elim

/-- Consequently the convolution of two such autocorrelations is supported
in the fourfold narrow dilate. -/
theorem comparisonWeight_support_four_mul
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {x : G} (hx : comparisonWeight C D x ≠ 0) :
    x ∈ (B.dilate (4 * eta)).carrier := by
  by_contra hxout
  apply hx
  rw [comparisonWeight, normalizedConvolution]
  apply Finset.sum_eq_zero
  intro y _
  let cCorr := normalizedDifferenceConvolution
    (normalizedIndicator C) (normalizedIndicator C)
  let dCorr := normalizedDifferenceConvolution
    (normalizedIndicator D) (normalizedIndicator D)
  by_cases hy : cCorr y = 0
  · exact mul_eq_zero.mpr (Or.inl (by simpa [cCorr] using hy))
  by_cases hxy : dCorr (x - y) = 0
  · exact mul_eq_zero.mpr (Or.inr (by simpa [dCorr] using hxy))
  have hyB : y ∈ (B.dilate (2 * eta)).carrier :=
    differenceIndicator_support_two_mul hC hCsmall hy
  have hxyB : x - y ∈ (B.dilate (2 * eta)).carrier :=
    differenceIndicator_support_two_mul hD hDsmall hxy
  have hmem := BohrData.add_mem_dilate hyB hxyB
  have heq : y + (x - y) = x := by abel
  rw [heq] at hmem
  exact (hxout (by
    simpa [show (2 : ℝ≥0) * eta + 2 * eta = 4 * eta by ring] using hmem)).elim

/-! ## The factor-two averaging step -/

/-- Majorization by a smoothed probability weight costs exactly a factor two
once every translate of the inner weight satisfies the same moment bound. -/
theorem weightedMoment_le_two_of_majorization
    (mu outer nu h : G → ℝ) (R : ℝ)
    (houter_nonneg : ∀ x, 0 ≤ outer x)
    (houter_mass : ∑ x : G, outer x = 1)
    (hh : ∀ x, 0 ≤ h x)
    (hmajor : ∀ x, mu x ≤ 2 * normalizedConvolution outer nu x)
    (htranslate : ∀ t : G, ∑ x : G, nu (x - t) * h x ≤ R) :
    ∑ x : G, mu x * h x ≤ 2 * R := by
  calc
    ∑ x : G, mu x * h x ≤
        ∑ x : G, (2 * normalizedConvolution outer nu x) * h x := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hmajor x) (hh x)
    _ = 2 * ∑ x : G, normalizedConvolution outer nu x * h x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 2 * ∑ t : G, outer t * ∑ x : G, nu (x - t) * h x := by
      apply congrArg (fun z : ℝ ↦ 2 * z)
      simp only [normalizedConvolution]
      calc
        ∑ x : G, (∑ y : G, outer y * nu (x - y)) * h x =
            ∑ x : G, ∑ y : G, (outer y * nu (x - y)) * h x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
        _ = ∑ t : G, ∑ x : G, (outer t * nu (x - t)) * h x :=
          Finset.sum_comm
        _ = ∑ t : G, outer t * ∑ x : G, nu (x - t) * h x := by
          apply Finset.sum_congr rfl
          intro t _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ ≤ 2 * ∑ t : G, outer t * R := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (htranslate t) (houter_nonneg t)
      · norm_num
    _ = 2 * R := by rw [← Finset.sum_mul, houter_mass, one_mul]

/-- The Bohr-majorization part of convolution comparison, separated from the
Fourier phase-removal input.  The next theorem discharges `hphase` for every
positive even exponent. -/
theorem convolutionComparison_moment_of_phaseRemoval
    {B : BohrData G} {rho eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsCoarselyRegularAt rho (4 * eta))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (p : ℕ) (f : G → ℂ)
    (hphase : ∀ t : G,
      ∑ x : G, comparisonWeight C D (x - t) * ‖convolution f f x‖ ^ p ≤
        ∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p) :
    ∑ x : G, normalizedIndicator (B.dilate rho).carrier x *
        ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  let nu := comparisonWeight C D
  let outer := normalizedIndicator (B.dilate (rho + 4 * eta)).carrier
  apply weightedMoment_le_two_of_majorization
      (normalizedIndicator (B.dilate rho).carrier) outer nu
      (fun x ↦ ‖convolution f f x‖ ^ p)
      (∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p)
  · exact normalizedIndicator_nonneg _
  · exact sum_normalizedIndicator (B.dilate (rho + 4 * eta)).carrier_nonempty
  · intro x
    positivity
  · intro x
    exact normalizedIndicator_le_two_mul_convolution_of_coarselyRegular
      hreg nu (comparisonWeight_nonneg C D) (sum_comparisonWeight hC hD)
      (fun t ht ↦ comparisonWeight_support_four_mul hC hD hCsmall hDsmall ht) x
  · exact hphase

/-- Rank-explicit specialization.  The numerical hypothesis says exactly
that the full fourfold support of the smoothing weight lies inside the
`1/(400 max(rank,1))` regularity window. -/
theorem convolutionComparison_moment_of_phaseRemoval_rankRegular
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (p : ℕ) (f : G → ℂ)
    (hphase : ∀ t : G,
      ∑ x : G, comparisonWeight C D (x - t) * ‖convolution f f x‖ ^ p ≤
        ∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p) :
    ∑ x : G, normalizedIndicator B.carrier x * ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  let nu := comparisonWeight C D
  let outer := normalizedIndicator (B.dilate (1 + 4 * eta)).carrier
  apply weightedMoment_le_two_of_majorization
      (normalizedIndicator B.carrier) outer nu
      (fun x ↦ ‖convolution f f x‖ ^ p)
      (∑ x : G, comparisonWeight C D x * ‖differenceConvolution f f x‖ ^ p)
  · exact normalizedIndicator_nonneg _
  · exact sum_normalizedIndicator (B.dilate (1 + 4 * eta)).carrier_nonempty
  · intro x
    positivity
  · intro x
    exact normalizedIndicator_le_two_mul_convolution_of_rankRegular
      hreg (by positivity : 0 < (4 : ℝ≥0) * eta) hnarrow nu
      (comparisonWeight_nonneg C D) (sum_comparisonWeight hC hD)
      (fun t ht ↦ comparisonWeight_support_four_mul hC hD hCsmall hDsmall ht) x
  · exact hphase

/-- **Convolution comparison on a coarse regular Bohr shell.**  For every
positive even exponent, additive convolution on the central Bohr weight is
controlled, with the exact factor two, by autocorrelation on the fourfold
autocorrelation weight. -/
theorem convolutionComparison_moment
    {B : BohrData G} {rho eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsCoarselyRegularAt rho (4 * eta))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (f : G → ℂ) :
    ∑ x : G, normalizedIndicator (B.dilate rho).carrier x *
        ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  apply convolutionComparison_moment_of_phaseRemoval hreg hC hD hCsmall hDsmall p f
  intro t
  apply LpOrthogonality.sum_translate_convolution_le_autocorrelation hp heven
      (comparisonWeight C D) (comparisonWeight_nonneg C D)
  · simpa only [comparisonWeight] using
      LpOrthogonality.spectrallyNonnegative_counting_autocorrelation_convolution
        (normalizedIndicator C) (normalizedIndicator D)

/-- Rank- and width-explicit form of `convolutionComparison_moment`.  This is
the form consumed by the balanced-restriction argument. -/
theorem convolutionComparison_moment_rankRegular
    {B : BohrData G} {eta : ℝ≥0} {C D : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCsmall : C ⊆ (B.dilate eta).carrier)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (f : G → ℂ) :
    ∑ x : G, normalizedIndicator B.carrier x * ‖convolution f f x‖ ^ p ≤
      2 * ∑ x : G, comparisonWeight C D x *
        ‖differenceConvolution f f x‖ ^ p := by
  apply convolutionComparison_moment_of_phaseRemoval_rankRegular
    hreg heta hnarrow hC hD hCsmall hDsmall p f
  intro t
  apply LpOrthogonality.sum_translate_convolution_le_autocorrelation hp heven
      (comparisonWeight C D) (comparisonWeight_nonneg C D)
  · simpa only [comparisonWeight] using
      LpOrthogonality.spectrallyNonnegative_counting_autocorrelation_convolution
        (normalizedIndicator C) (normalizedIndicator D)

end

end ConvolutionComparison

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BalancedRestrictionAssembly.lean` -/

section
/-! # Concrete localized-unbalancing assembly for balanced restriction -/

open _root_.Finset Fintype _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped BigOperators ComplexConjugate ComplexOrder _root_.ENNReal _root_.NNReal Pointwise

namespace BalancedRestrictionAssembly

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

lemma normalizedConvolution_eq_ddconv (f g : G → ℝ) :
    normalizedConvolution f g = f ∗ᵈ g := by
  funext x
  rw [normalizedConvolution, ddconv_eq_sum_sub']

lemma normalizedDifferenceConvolution_eq_dddconv (f g : G → ℝ) :
    normalizedDifferenceConvolution f g = f ○ᵈ g := by
  funext x
  rw [normalizedDifferenceConvolution, dddconv_eq_sum_sub']
  simp

/-- The NNReal autocorrelation weight used by localized unbalancing is
exactly the real counting-convolution weight used by the Fourier comparison. -/
theorem coe_smoothingWeight_eq_comparisonWeight (D E : Finset G) :
    ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E : G → ℝ) =
      ConvolutionComparison.comparisonWeight D E := by
  rw [ConvolutionComparison.comparisonWeight,
    normalizedConvolution_eq_ddconv,
    normalizedDifferenceConvolution_eq_dddconv,
    normalizedDifferenceConvolution_eq_dddconv]
  simp only [LocalizedUnbalancing.smoothingWeight,
    LocalizedUnbalancing.smoothingBase, NNReal.coe_comp_dddconv,
    NNReal.coe_comp_ddconv, NNReal.coe_comp_mu,
    LocalizedUnbalancing.mu_eq_normalizedIndicator]
  exact (dddconv_ddconv_dddconv_comm
    (normalizedIndicator D) (normalizedIndicator D)
    (normalizedIndicator E) (normalizedIndicator E)).symm

private lemma abs_normalizedConvolution_pow
    (a : G → ℝ) (p : ℕ) (x : G) :
    |normalizedConvolution a a x| ^ p =
      (Fintype.card G : ℝ) ^ p *
        ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  have h := congrArg norm
    (LpOrthogonality.ofReal_countingConvolution a a x)
  simp only [Complex.norm_real, norm_mul, Complex.norm_natCast] at h
  have h' : |normalizedConvolution a a x| =
      (Fintype.card G : ℝ) *
        ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ := by
    simpa only [Real.norm_eq_abs] using h
  rw [h', mul_pow]

private lemma abs_normalizedDifferenceConvolution_pow
    (a : G → ℝ) (p : ℕ) (x : G) :
    |normalizedDifferenceConvolution a a x| ^ p =
      (Fintype.card G : ℝ) ^ p *
        ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  have h := congrArg norm
    (LpOrthogonality.ofReal_countingAutocorrelation a x)
  simp only [Complex.norm_real, norm_mul, Complex.norm_natCast] at h
  have h' : |normalizedDifferenceConvolution a a x| =
      (Fintype.card G : ℝ) *
        ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ := by
    simpa only [Real.norm_eq_abs] using h
  rw [h', mul_pow]

private lemma weightedAbsMoment_normalizedConvolution_eq
    (w a : G → ℝ) (p : ℕ) :
    weightedAbsMoment w (normalizedConvolution a a) p =
      (Fintype.card G : ℝ) ^ p *
        ∑ x : G, w x *
          ‖FiniteFourier.convolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  unfold weightedAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_normalizedConvolution_pow]
  ring

private lemma weightedAbsMoment_normalizedDifferenceConvolution_eq
    (w a : G → ℝ) (p : ℕ) :
    weightedAbsMoment w (normalizedDifferenceConvolution a a) p =
      (Fintype.card G : ℝ) ^ p *
        ∑ x : G, w x *
          ‖FiniteFourier.differenceConvolution ((↑) ∘ a) ((↑) ∘ a) x‖ ^ p := by
  unfold weightedAbsMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_normalizedDifferenceConvolution_pow]
  ring

/-- Concrete factor-two moment comparison in the physical normalization
used by localized unbalancing.  The ambient-cardinality factors on the
convolution and autocorrelation sides cancel exactly. -/
theorem concrete_comparison_moment
    {B : BohrData G} {eta : ℝ≥0} {D E : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (hEsmall : E ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : p ≠ 0) (heven : Even p) (a : G → ℝ) :
    weightedAbsMoment (normalizedIndicator B.carrier)
        (normalizedConvolution a a) p ≤
      2 * weightedAbsMoment
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (normalizedDifferenceConvolution a a) p := by
  have h := ConvolutionComparison.convolutionComparison_moment_rankRegular
    hreg heta hnarrow hD hE hDsmall hEsmall hp heven ((↑) ∘ a)
  rw [← coe_smoothingWeight_eq_comparisonWeight D E] at h
  have hscale : 0 ≤ (Fintype.card G : ℝ) ^ p := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hscale
  rw [weightedAbsMoment_normalizedConvolution_eq,
    weightedAbsMoment_normalizedDifferenceConvolution_eq]
  nlinarith

/-- The concrete comparison in the weighted `L^p` form consumed by the
stopping contradiction. -/
theorem concrete_comparison_lp
    {B : BohrData G} {eta : ℝ≥0} {D E : Finset G}
    (hreg : B.IsRankRegular) (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (B.dilate eta).carrier)
    (hEsmall : E ⊆ (B.dilate eta).carrier)
    {p : ℕ} (hp : 0 < p) (heven : Even p) (a : G → ℝ) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator B.carrier)
        (normalizedConvolution a a) p ≤
      2 * BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (normalizedDifferenceConvolution a a) p := by
  have houter : BalancedRestriction.ProbabilityWeight
      (normalizedIndicator B.carrier) :=
    ⟨normalizedIndicator_nonneg B.carrier,
      sum_normalizedIndicator B.carrier_nonempty⟩
  have hnu : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) :=
    ⟨fun x ↦ by
      exact_mod_cast (show 0 ≤ LocalizedUnbalancing.smoothingWeight D E x by
        exact LocalizedUnbalancing.smoothingWeight_nonneg D E x),
      by
        simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ))
          (LocalizedUnbalancing.smoothingWeight_sum hD hE)⟩
  apply BalancedRestriction.weightedLpNorm_le_two_of_moment_le_two
    houter hnu hp
  exact concrete_comparison_moment hreg heta hnarrow hD hE hDsmall hEsmall
    hp.ne' heven a

/-- Specialization of the stopping contradiction to the proved localized
unbalancing theorem. -/
theorem balanced_of_localized_unbalancing
    {B : BohrData G} (hreg : B.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAB : A ⊆ B.carrier)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max B.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (B.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (B.carrier.card : ℝ)⁻¹ *
          (200 * ((max B.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (B.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    {outerWeight balancedConvolution : G → ℝ}
    (houter : BalancedRestriction.ProbabilityWeight outerWeight)
    (hcomparison :
      BalancedRestriction.weightedLpNorm outerWeight balancedConvolution
          (BalancedRestriction.comparisonExponent p) ≤
        2 * BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          ((μ_[ℝ] A - μ B.carrier) ○ᵈ (μ A - μ B.carrier))
          (BalancedRestriction.comparisonExponent p))
    (hstopping :
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) <
        (1 + epsilon / 8) * (B.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm outerWeight balancedConvolution p ≤
      epsilon * (B.carrier.card : ℝ)⁻¹ := by
  let nu := LocalizedUnbalancing.smoothingWeight D E
  have hmass : ∑ x : G, nu x = 1 :=
    LocalizedUnbalancing.smoothingWeight_sum hD hE
  have hnu : BalancedRestriction.ProbabilityWeight ((↑) ∘ nu) :=
    ⟨fun x ↦ by
      exact_mod_cast (show 0 ≤ nu x by
        exact LocalizedUnbalancing.smoothingWeight_nonneg D E x),
      by simpa using congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) hmass⟩
  have hcard : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  have hmain : 0 < (B.carrier.card : ℝ)⁻¹ := inv_pos.mpr hcard
  apply BalancedRestriction.balanced_convolution_of_stopping
      houter hnu hepsilon hmain hp (by simpa [nu] using hcomparison) _
      (by simpa [nu] using hstopping)
  intro hlarge
  obtain ⟨r, hr, _hreven, hrQ, hrlarge⟩ :=
    LocalizedUnbalancing.localized_unbalancing hreg hA hAB hD hE hkappa
      hsupport hepsilon hepsilon_one hwidth hp (by simpa [nu] using hlarge)
  exact ⟨r, hr, hrQ, by simpa [nu] using hrlarge⟩

end
end BalancedRestrictionAssembly

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/Bookkeeping.lean` -/

section
/-!
# Quantitative bookkeeping for the final Erdős 140 assembly

This file contains only stable numerical/volumetric adapters. In particular,
the first lemma iterates the already proved rank-only half-dilate estimate.
It is the form needed to compare an old Bohr carrier with a much smaller
explicit scalar dilate in the terminal density-step construction.
-/

open _root_.Finset
open scoped _root_.NNReal Pointwise

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end BohrData

/-- A lower bound for the relative cardinality of X gives the exact
upper bound on the local Chang dimension used by the terminal producer.
The hypothesis is written without division so downstream finite-cardinality
arguments do not have to clear denominators twice. -/
theorem localChangDimension_le_of_mul_card_le
    {G : Type*} [AddCommGroup G] [Fintype G]
    (B : BohrData G) (X : Finset G) {beta eta : ℝ}
    (hbeta : 0 < beta) (heta : 0 < eta)
    (hX : X.Nonempty)
    (hcard : beta * (B.carrier.card : ℝ) ≤ (X.card : ℝ)) :
    RelativeChangSanders.localChangDimension B X eta ≤
      2 * (1 + Real.log (2 / beta)) / eta ^ 2 := by
  have hBpos : (0 : ℝ) < B.carrier.card := by
    exact_mod_cast B.carrier_nonempty.card_pos
  have hXpos : (0 : ℝ) < X.card := by
    exact_mod_cast hX.card_pos
  have hratio :
      2 * (B.carrier.card : ℝ) / X.card ≤ 2 / beta := by
    rw [div_le_div_iff₀ hXpos hbeta]
    nlinarith
  have hargpos : 0 < 2 * (B.carrier.card : ℝ) / X.card := by
    positivity
  have hlog :
      Real.log (2 * (B.carrier.card : ℝ) / X.card) ≤
        Real.log (2 / beta) :=
    Real.log_le_log hargpos hratio
  have hetaSq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [RelativeChangSanders.localChangDimension]
  apply (div_le_div_iff_of_pos_right hetaSq).2
  nlinarith

/-- Half-spectrum specialization of the local Chang-dimension bound. -/
theorem localChangDimension_half_le_of_mul_card_le
    {G : Type*} [AddCommGroup G] [Fintype G]
    (B : BohrData G) (X : Finset G) {beta : ℝ}
    (hbeta : 0 < beta) (hX : X.Nonempty)
    (hcard : beta * (B.carrier.card : ℝ) ≤ (X.card : ℝ)) :
    RelativeChangSanders.localChangDimension B X (1 / 2) ≤
      8 * (1 + Real.log (2 / beta)) := by
  have h :=
    localChangDimension_le_of_mul_card_le B X hbeta
      (by norm_num : (0 : ℝ) < 1 / 2) hX hcard
  convert h using 1
  ring

/-- A real-valued cardinal bound can be turned into the natural ceiling
needed for a rank-cost field. -/
theorem card_le_natCeil_of_cast_card_le
    {α : Type*} [Fintype α] (S : Finset α) {D : ℝ}
    (hcard : (S.card : ℝ) ≤ D) :
    S.card ≤ ⌈D⌉₊ := by
  exact_mod_cast hcard.trans (Nat.le_ceil D)

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/FinalAssembly.lean` -/

section
/-!
# Final dense-pair assembly

The terminal Holder step uses two Bohr carriers with different jobs.  The
baseline carrier controls the balanced function and the main term, while the
weight carrier is the doubled middle-fibre carrier on which the Holder norm
is measured.  Keeping those roles separate is essential for the exact
normalizations in the cyclic counting endpoint.
-/

open _root_.Finset Fintype _root_.Function
open scoped BigOperators _root_.NNReal

namespace FinalAssembly

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The scaled balanced convolution appearing in the Holder endpoint. -/
def scaledBalanced (K : BohrData G) (A : Finset G) : G → ℝ :=
  (Fintype.card G : ℝ) •
    normalizedConvolution (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)

/-- Concrete two-carrier balanced restriction.  The comparison theorem is
run with the weight carrier, while localized unbalancing is run with the
baseline carrier. -/
theorem balanced_of_twoBohr_concrete_stopping
    {K W : BohrData G} (hKreg : K.IsRankRegular)
    (hWreg : W.IsRankRegular)
    {A : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hnarrow : 4 * eta ≤
      1 / (400 * (max W.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (W.dilate eta).carrier)
    (hEsmall : E ⊆ (W.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappa : kappa ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    (hsupport : ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (K.dilate kappa).carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon_one : epsilon ≤ 1)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
        epsilon / 8 * (K.carrier.card : ℝ)⁻¹)
    {p : ℕ} (hp : 0 < p)
    (hstopping :
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] A ○ᵈ μ A) (BalancedRestriction.stoppingExponent epsilon p) <
        (1 + epsilon / 8) * (K.carrier.card : ℝ)⁻¹) :
    BalancedRestriction.weightedLpNorm (normalizedIndicator W.carrier)
        (normalizedConvolution
          (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)) p ≤
      epsilon * (K.carrier.card : ℝ)⁻¹ := by
  let a : G → ℝ := μ_[ℝ] A - μ K.carrier
  have hq : 0 < BalancedRestriction.comparisonExponent p :=
    Nat.mul_pos (by norm_num) hp
  have hcomparison :=
    BalancedRestrictionAssembly.concrete_comparison_lp hWreg heta hnarrow
      hD hE hDsmall hEsmall hq
      (BalancedRestriction.comparisonExponent_even p) a
  rw [BalancedRestrictionAssembly.normalizedDifferenceConvolution_eq_dddconv]
    at hcomparison
  apply BalancedRestrictionAssembly.balanced_of_localized_unbalancing
      hKreg hA hAK hD hE hkappa hsupport hepsilon hepsilon_one hwidth hp
      ⟨normalizedIndicator_nonneg W.carrier,
        sum_normalizedIndicator W.carrier_nonempty⟩
  · simpa [a] using hcomparison
  · exact hstopping

/-! ## Rank-regular located states

The quantitative narrowing theorem is rank-regular, whereas the generic
located state remembers only coarse shell regularity.  The final recursion
therefore carries the stronger invariant explicitly. -/

/-- A located restriction together with the rank-regularity needed by the
next quantitative narrowing step. -/
structure RankRegularLocatedRestriction (original : Finset G) where
  located : DensityStep.LocatedRestriction original
  outer_one : located.restriction.outer = 1
  rankRegular : located.restriction.bohr.IsRankRegular

namespace RankRegularLocatedRestriction

def density {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℝ := s.located.density

def rank {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℕ := s.located.rank

def card {original : Finset G} (s : RankRegularLocatedRestriction original) :
    ℕ := s.located.card

lemma density_pos {original : Finset G} (s : RankRegularLocatedRestriction original) :
    0 < s.density := s.located.density_pos

lemma density_nonneg {original : Finset G} (s : RankRegularLocatedRestriction original) :
    0 ≤ s.density := s.density_pos.le

end RankRegularLocatedRestriction

/-- Two actual rank-regular children and their quantitative losses.  Unlike
DensityStep.NarrowingPackage, this uses the proved rank-regular Bourgain
alternative directly and does not ask for an unrelated exact plateau. -/
structure RankRegularNarrowingPackage
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    (epsilon sizeCost : ℝ) (rankCost : ℕ) where
  kappa : ℝ≥0
  kappa_small :
    kappa ≤
      1 / (100 * (max s.located.restriction.bohr.rank 1 : ℕ) : ℝ≥0)
  childOne : DensityStep.RegularChild (G := G)
  childTwo : DensityStep.RegularChild (G := G)
  childOne_outer_one : childOne.outer = 1
  childTwo_outer_one : childTwo.outer = 1
  childOne_rankRegular : childOne.bohr.IsRankRegular
  childTwo_rankRegular : childTwo.bohr.IsRankRegular
  smallOne : childOne.carrier ⊆
    (s.located.restriction.bohr.dilate kappa).carrier
  smallTwo : childTwo.carrier ⊆
    (s.located.restriction.bohr.dilate kappa).carrier
  narrowing_small :
    400 * ((max s.located.restriction.bohr.rank 1 : ℕ) : ℝ) * (kappa : ℝ) ≤
      epsilon *
        relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier / 4
  rankOne : childOne.bohr.rank ≤ s.rank + rankCost
  rankTwo : childTwo.bohr.rank ≤ s.rank + rankCost
  cardOne : Real.exp (-sizeCost) * (s.card : ℝ) ≤ childOne.carrier.card
  cardTwo : Real.exp (-sizeCost) * (s.card : ℝ) ≤ childTwo.carrier.card

/-- Rank-regular narrowing preserves rank-regularity on the increment
branch and retains the honest dense-pair branch on the same two children. -/
theorem densePair_or_rankRegular_increment
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (hepsilon : 0 < epsilon)
    (P : RankRegularNarrowingPackage s epsilon sizeCost rankCost) :
    DensityStep.HasDensePair s.located P.childOne P.childTwo epsilon ∨
      ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.located.restriction t.located.restriction := by
  have hA := s.located.restriction.nonempty
  have hAK :
      s.located.restriction.set ⊆ s.located.restriction.bohr.carrier := by
    simpa [BohrStopping.RegularRestriction.ambient, s.outer_one] using
      s.located.restriction.subset_carrier
  have hdensityEq :
      relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier = s.located.density := by
    unfold DensityStep.LocatedRestriction.density BohrStopping.RegularRestriction.density
      relativeDensityOn BohrStopping.RegularRestriction.ambient
    simp [s.outer_one]
  rcases bohr_narrowing_alternative_of_rankRegular
      s.rankRegular P.kappa_small hA hAK
      P.childOne.carrier_nonempty P.childTwo.carrier_nonempty
      P.smallOne P.smallTwo hepsilon P.narrowing_small with
    hdense | hincOne | hincTwo
  · left
    rw [hdensityEq] at hdense
    simpa [DensityStep.HasDensePair, DensityStep.LocatedRestriction.ambient,
      DensityStep.LocatedRestriction.density,
      BohrStopping.RegularRestriction.density,
      BohrStopping.RegularRestriction.ambient, s.outer_one] using hdense
  · right
    obtain ⟨x, hx⟩ := hincOne
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.located.restriction.set
        P.childOne.carrier x := by
      have hs : 0 < s.located.density := s.located.density_pos
      have hq : 0 < (1 + epsilon / 2 : ℝ) := by nlinarith
      exact (mul_pos hq hs).trans_le (by simpa using hx)
    let u := DensityStep.narrowLocated s.located P.childOne x hpos
    refine ⟨{ located := u, outer_one := ?_, rankRegular := ?_ }, ?_⟩
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childOne_outer_one
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childOne_rankRegular
    · apply DensityStep.narrowLocated_isControlledIncrement
        s.located P.childOne x hpos
      · simpa [DensityStep.LocatedRestriction.density,
          BohrStopping.RegularRestriction.density,
          BohrStopping.RegularRestriction.ambient] using hx
      · exact P.rankOne
      · exact P.cardOne
  · right
    obtain ⟨x, hx⟩ := hincTwo
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.located.restriction.set
        P.childTwo.carrier x := by
      have hs : 0 < s.located.density := s.located.density_pos
      have hq : 0 < (1 + epsilon / 2 : ℝ) := by nlinarith
      exact (mul_pos hq hs).trans_le (by simpa using hx)
    let u := DensityStep.narrowLocated s.located P.childTwo x hpos
    refine ⟨{ located := u, outer_one := ?_, rankRegular := ?_ }, ?_⟩
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childTwo_outer_one
    · simpa [u, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using P.childTwo_rankRegular
    · apply DensityStep.narrowLocated_isControlledIncrement
        s.located P.childTwo x hpos
      · simpa [DensityStep.LocatedRestriction.density,
          BohrStopping.RegularRestriction.density,
          BohrStopping.RegularRestriction.ambient] using hx
      · exact P.rankTwo
      · exact P.cardTwo

/-! ## Raw dense-pair Holder endpoint

The old GroupCount constructor takes a NarrowingPackage only to name its two
children.  The rank-regular recursion uses the children directly, so the
same finite-set argument is repeated here without a plateau-shaped wrapper.
-/

def rawDensePairEndpointSet
    {original : Finset G} {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childOne.carrier
    (GroupCount.densePairPoint h)

def rawDensePairMiddleSet
    {original : Finset G} {s : DensityStep.LocatedRestriction original}
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (h : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childTwo.carrier
    (GroupCount.densePairPoint h)

/-- Generic Holder certificate from two actual children and their common
dense translate. -/
noncomputable def holderCountCertificateOfRawDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {childOne childTwo : DensityStep.RegularChild (G := G)} {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (_hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    {p : ℕ} (hp : 0 < p) (f : G → ℝ)
    (hpDensity : (2 / 3 : ℝ) ^ p ≤ GroupCount.densePairDensity s epsilon)
    (happrox :
      |(GroupCount.normalizedMixedProgression
            (rawDensePairEndpointSet hdense) (rawDensePairMiddleSet hdense) -
          (Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) -
          HolderLifting.pairing f
            (GroupCount.doubledFinset (rawDensePairMiddleSet hdense))| ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8)
    (hbalanced :
      BalancedRestriction.weightedLpNorm
          (normalizedIndicator (GroupCount.doubledFinset childTwo.carrier)) f p ≤
        ((Fintype.card G : ℝ) / (#childOne.carrier : ℝ)) / 8) :
    GroupCount.HolderCountCertificate original := by
  let x : G := GroupCount.densePairPoint hdense
  let A' : Finset G := rawDensePairEndpointSet hdense
  let A'' : Finset G := rawDensePairMiddleSet hdense
  let B : Finset G := childOne.carrier
  let B' : Finset G := childTwo.carrier
  let alpha : ℝ := GroupCount.densePairDensity s epsilon
  have hOne : alpha ≤ localDensity s.restriction.set B x := by
    simpa [alpha, x, B, GroupCount.densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  have hTwo : alpha ≤ localDensity s.restriction.set B' x := by
    simpa [alpha, x, B', GroupCount.densePairDensity] using
      GroupCount.densePairPoint_density_two hdense
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hA' : A'.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' : A''.Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hA''B' : A'' ⊆ B' := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := childTwo.bohr) (rho := childTwo.outer)
      (A := s.restriction.set) (C := childTwo.carrier)
      (x := x) (fun _ hz ↦ hz)
  have hA'trans : ∀ z ∈ A', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hA''trans : ∀ z ∈ A'', z - (s.shift - x) ∈ original := by
    intro z hz
    have hzSource : x + z ∈ s.restriction.set :=
      (DensityStep.mem_narrowingSet.mp hz).2
    have hs := s.subset_original (x + z) hzSource
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  have hDensityOne : alpha * (#B : ℝ) ≤ (#A' : ℝ) := by
    have hBpos : (0 : ℝ) < #B := by exact_mod_cast childOne.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childOne.carrier_nonempty x] at hOne
    exact (le_div_iff₀ hBpos).mp hOne
  have hDensityTwo : alpha * (#B' : ℝ) ≤ (#A'' : ℝ) := by
    have hB'pos : (0 : ℝ) < #B' := by exact_mod_cast childTwo.carrier_nonempty.card_pos
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      childTwo.carrier_nonempty x] at hTwo
    exact (le_div_iff₀ hB'pos).mp hTwo
  have hRelative :
      (2 / 3 : ℝ) ^ p ≤ HolderLifting.relativeDensity A'' B' := by
    calc
      (2 / 3 : ℝ) ^ p ≤ alpha := hpDensity
      _ ≤ localDensity s.restriction.set B' x := hTwo
      _ = HolderLifting.relativeDensity A'' B' := by
        rw [DensityStep.localDensity_eq_card_narrowingSet_div
          childTwo.carrier_nonempty x]
        rfl
  have hDoubledB' : (GroupCount.doubledFinset B').Nonempty :=
    GroupCount.doubledFinset_nonempty childTwo.carrier_nonempty
  have hMoment :
      HolderLifting.localMoment (GroupCount.doubledFinset B') p f ≤
        (((Fintype.card G : ℝ) / (#B : ℝ)) / 8) ^ p := by
    apply GroupCount.localMoment_le_of_weightedLpNorm_le hDoubledB' hp f (by positivity)
    simpa [B, B'] using hbalanced
  exact
    { A' := A'
      A'' := A''
      B := B
      B' := B'
      translate := s.shift - x
      alpha := alpha
      p := p
      f := f
      A'_nonempty := hA'
      A''_nonempty := hA''
      B_nonempty := childOne.carrier_nonempty
      A''_subset_B' := hA''B'
      A'_sub_translate := hA'trans
      A''_sub_translate := hA''trans
      alpha_nonneg := halpha.le
      A'_density := hDensityOne
      A''_density := hDensityTwo
      p_pos := hp
      doubled_density := hRelative
      approximation := by simpa [A', A'', B] using happrox
      balanced_moment := hMoment }

/-- Two-Bohr analytic output for the raw rank-regular child package.  This
is the target interface for the concrete localized-almost-periodicity
construction. -/
structure RawTwoBohrEndpointPackage
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s epsilon sizeCost rankCost)
    (hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo epsilon) where
  base : BohrData G
  weight : BohrData G
  base_regular : base.IsRankRegular
  weight_regular : weight.IsRankRegular
  base_carrier : base.carrier = P.childOne.carrier
  weight_carrier :
    weight.carrier = GroupCount.doubledFinset P.childTwo.carrier
  endpoint_nonempty : (rawDensePairEndpointSet hdense).Nonempty
  endpoint_subset : rawDensePairEndpointSet hdense ⊆ base.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow : 4 * eta ≤
    1 / (400 * (max weight.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (weight.dilate eta).carrier
  E_small : E ⊆ (weight.dilate eta).carrier
  kappa : ℝ≥0
  rank_width : kappa ≤ 1 / (100 * (max base.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (base.dilate kappa).carrier
  boundary_width :
    2 * (((rawDensePairEndpointSet hdense).card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (base.carrier.card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (base.carrier.card : ℝ)⁻¹
  density_power :
    (2 / 3 : ℝ) ^ p ≤ GroupCount.densePairDensity s.located epsilon
  approximation :
    |(GroupCount.normalizedMixedProgression
          (rawDensePairEndpointSet hdense) (rawDensePairMiddleSet hdense) -
        (Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced base (rawDensePairEndpointSet hdense))
          (GroupCount.doubledFinset (rawDensePairMiddleSet hdense))| ≤
      ((Fintype.card G : ℝ) / (#P.childOne.carrier : ℝ)) / 8
  highNorm_increment :
    (1 + (1 / 8 : ℝ) / 8) * (base.carrier.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
          (μ_[ℝ] (rawDensePairEndpointSet hdense) ○ᵈ
            μ (rawDensePairEndpointSet hdense))
          (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) →
      ∃ t : RankRegularLocatedRestriction original,
        (257 / 256 : ℝ) *
            GroupCount.densePairDensity s.located epsilon ≤ t.density ∧
        t.rank ≤ s.rank + rankCost ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- The raw two-Bohr package yields the exact local terminal data after the
balanced stopping inequality has been proved. -/
noncomputable def locatedTerminalDataOfRawTwoBohr
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo
      (1 / 512 : ℝ))
    (hp : 0 < p)
    (Q : RawTwoBohrEndpointPackage (p := p) s P hdense)
    (hraw :
      BalancedRestriction.weightedLpNorm (normalizedIndicator Q.weight.carrier)
          (normalizedConvolution
            (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
            (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier)) p ≤
        (1 / 8 : ℝ) * (Q.base.carrier.card : ℝ)⁻¹) :
    LocatedHolderTerminalData s.located K d := by
  let c := holderCountCertificateOfRawDensePair s.located hdense
    (by norm_num) (by norm_num) hp
    (scaledBalanced Q.base (rawDensePairEndpointSet hdense))
    Q.density_power Q.approximation (by
      let w : G → ℝ≥0 := μ Q.weight.carrier
      have hscale :=
        LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
          (normalizedConvolution
            (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
            (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier))
          (Fintype.card G : ℝ) (by positivity) hp
      have hscale' :
          BalancedRestriction.weightedLpNorm
              (normalizedIndicator Q.weight.carrier)
              (scaledBalanced Q.base (rawDensePairEndpointSet hdense)) p =
            (Fintype.card G : ℝ) *
              BalancedRestriction.weightedLpNorm
                (normalizedIndicator Q.weight.carrier)
                (normalizedConvolution
                  (μ_[ℝ] (rawDensePairEndpointSet hdense) - μ Q.base.carrier)
                  (μ (rawDensePairEndpointSet hdense) - μ Q.base.carrier)) p := by
        simpa only [w, NNReal.coe_comp_mu,
          LocalizedUnbalancing.mu_eq_normalizedIndicator,
          scaledBalanced] using hscale
      have hscaled :
          BalancedRestriction.weightedLpNorm
              (normalizedIndicator Q.weight.carrier)
              (scaledBalanced Q.base (rawDensePairEndpointSet hdense)) p ≤
            (Fintype.card G : ℝ) *
              ((1 / 8 : ℝ) * (Q.base.carrier.card : ℝ)⁻¹) := by
        rw [hscale']
        exact mul_le_mul_of_nonneg_left hraw (by positivity)
      rw [Q.weight_carrier] at hscaled
      simpa [Q.base_carrier, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hscaled)
  refine
    { certificate := c
      alpha_lower := ?_
      B_card := ?_
      B'_card := ?_ }
  · change (3 / 4 : ℝ) * s.located.density ≤
      GroupCount.densePairDensity s.located (1 / 512 : ℝ)
    simp only [GroupCount.densePairDensity]
    nlinarith [s.located.density_pos.le]
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childOne.carrier : ℝ)
    exact P.cardOne
  · change Real.exp (-(K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
        (s.card : ℝ) ≤ (#P.childTwo.carrier : ℝ)
    exact P.cardTwo

/-- Honest one-step terminal-or-increment result for a rank-regular state.
The dense-pair loss is 1/512, the balanced-restriction loss is 1/8, and the
composed gain is the fixed 1025/1024 used by the global stopping argument. -/
theorem terminalData_or_rankRegular_increment
    {original : Finset G} (s : RankRegularLocatedRestriction original)
    {K : ℝ} {d rankCost p : ℕ}
    (P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
      (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost)
    (hp : 0 < p)
    (hendpoint :
      ∀ hdense : DensityStep.HasDensePair s.located P.childOne P.childTwo
          (1 / 512 : ℝ),
        Nonempty (RawTwoBohrEndpointPackage (p := p) s P hdense)) :
    Nonempty (LocatedHolderTerminalData s.located K d) ∨
      ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)
          s.located.restriction t.located.restriction := by
  rcases densePair_or_rankRegular_increment s
      (by norm_num : (0 : ℝ) < 1 / 512) P with hpair | hincrement
  · obtain ⟨Q⟩ := hendpoint hpair
    by_cases hhigh :
        (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
            (μ_[ℝ] (rawDensePairEndpointSet hpair) ○ᵈ
              μ (rawDensePairEndpointSet hpair))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p)
    · right
      obtain ⟨u, hdensity, hurank, hucard⟩ := Q.highNorm_increment hhigh
      refine ⟨u, ?_, hurank, hucard⟩
      calc
        (1025 / 1024 : ℝ) * s.located.density ≤
            (257 / 256 : ℝ) *
              GroupCount.densePairDensity s.located (1 / 512 : ℝ) := by
          simp only [GroupCount.densePairDensity]
          nlinarith [s.located.density_pos.le]
        _ ≤ u.density := hdensity
    · left
      have hstop :
          BalancedRestriction.weightedLpNorm
              ((↑) ∘ LocalizedUnbalancing.smoothingWeight Q.D Q.E)
              (μ_[ℝ] (rawDensePairEndpointSet hpair) ○ᵈ
                μ (rawDensePairEndpointSet hpair))
              (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) <
            (1 + (1 / 8 : ℝ) / 8) * (Q.base.carrier.card : ℝ)⁻¹ :=
        lt_of_not_ge hhigh
      have hraw := balanced_of_twoBohr_concrete_stopping Q.base_regular
        Q.weight_regular Q.endpoint_nonempty Q.endpoint_subset Q.eta_pos
        Q.eta_narrow Q.D_nonempty Q.E_nonempty Q.D_small Q.E_small
        Q.rank_width Q.smoothing_support (by norm_num) (by norm_num)
        Q.boundary_width hp hstop
      exact ⟨locatedTerminalDataOfRawTwoBohr s P hpair hp Q hraw⟩
  · right
    obtain ⟨u, hu⟩ := hincrement
    refine ⟨u, ?_⟩
    simpa only [show (1 + (1 / 512 : ℝ) / 2) =
        (1025 / 1024 : ℝ) by norm_num] using hu

/-! ## Rank-regular finite stopping

This recursion is the rank-regular replacement for the generic located
stopping theorem.  It keeps the stronger invariant in the state rather than
forgetting it after the first child. -/

inductive RankRegularControlledChain {original : Finset G}
    (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) :
    ℕ → RankRegularLocatedRestriction original →
      RankRegularLocatedRestriction original → Prop
  | nil (s : RankRegularLocatedRestriction original) :
      RankRegularControlledChain q rankCost sizeCost 0 s s
  | cons {n : ℕ} {s t u : RankRegularLocatedRestriction original}
      (hst : BohrStopping.IsControlledIncrement q rankCost sizeCost
        s.located.restriction t.located.restriction)
      (htu : RankRegularControlledChain q rankCost sizeCost n t u) :
      RankRegularControlledChain q rankCost sizeCost (n + 1) s u

namespace RankRegularControlledChain

theorem forget {original : Finset G} {q sizeCost : ℝ} {rankCost n : ℕ}
    {s t : RankRegularLocatedRestriction original}
    (h : RankRegularControlledChain q rankCost sizeCost n s t) :
    DensityStep.LocatedControlledChain q rankCost sizeCost n s.located t.located := by
  induction h with
  | nil s => exact DensityStep.LocatedControlledChain.nil s.located
  | cons hst _ ih => exact DensityStep.LocatedControlledChain.cons hst ih

end RankRegularControlledChain

/-! ## Cyclic initial rank-regular state

The empty-frequency Bohr datum is rank-regular because every one of its
dilates is the whole group. -/

theorem universalBohrData_rankRegular
    (G : Type*) [AddCommGroup G] [Fintype G] :
    (universalBohrData G).IsRankRegular := by
  intro kappa _hkappa
  simp only [universalBohrData_rank, show max 0 1 = 1 by omega,
    Nat.cast_one]
  rw [universalBohrData_carrier_self]
  simp only [universalBohrData_carrier]
  have hcard : (0 : ℝ) ≤ Fintype.card G := by positivity
  constructor <;> nlinarith [show (0 : ℝ) ≤ kappa by positivity]

/-- The genuine cyclic initial restriction with its rank-regular invariant. -/
noncomputable def cyclicInitialRankRegularLocated (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    RankRegularLocatedRestriction A where
  located := cyclicInitialLocated N A hA
  outer_one := rfl
  rankRegular := universalBohrData_rankRegular (ZMod (intervalModulus N))

@[simp] theorem cyclicInitialRankRegularLocated_density (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).density =
      (#A : ℝ) / (intervalModulus N : ℕ) := by
  exact cyclicInitialLocated_density N A hA

@[simp] theorem cyclicInitialRankRegularLocated_rank (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).rank = 0 := by
  exact cyclicInitialLocated_rank N A hA

@[simp] theorem cyclicInitialRankRegularLocated_card (N : ℕ)
    (A : Finset (ZMod (intervalModulus N))) (hA : A.Nonempty) :
    (cyclicInitialRankRegularLocated N A hA).card = intervalModulus N := by
  exact cyclicInitialLocated_card N A hA

/-- Bounded rank-regular stopping with the dyadic and rank invariants exposed
at each used-step index.  This is the form consumed by the concrete supplier,
whose quantitative construction only needs those two bounds. -/
theorem exists_terminal_rankRegular_chain_bounded_aux
    {original : Finset G}
    {Terminal : RankRegularLocatedRestriction original → Prop}
    {q lower sizeCost : ℝ} {rankCost total used remaining : ℕ}
    (hq : 1 ≤ q)
    (hbudget : used + remaining ≤ total)
    (hstep : ∀ n < total, ∀ s : RankRegularLocatedRestriction original,
      lower ≤ s.density →
      s.rank ≤ n * rankCost →
      Terminal s ∨ ∃ t : RankRegularLocatedRestriction original,
        BohrStopping.IsControlledIncrement q rankCost sizeCost
          s.located.restriction t.located.restriction)
    (initial : RankRegularLocatedRestriction original)
    (hscale : lower ≤ initial.density)
    (hrank : initial.rank ≤ used * rankCost)
    (hgrowth : 1 < q ^ remaining * initial.density) :
    ∃ n ≤ remaining, ∃ t : RankRegularLocatedRestriction original,
      RankRegularControlledChain q rankCost sizeCost n initial t ∧
      Terminal t := by
  induction remaining generalizing initial used with
  | zero =>
      have hs := initial.located.density_le_one
      simp only [pow_zero, one_mul] at hgrowth
      exact (not_lt_of_ge hs hgrowth).elim
  | succ remaining ih =>
      have hused : used < total := by omega
      rcases hstep used hused initial hscale hrank with hterminal | ⟨t, hst⟩
      · exact ⟨0, by omega, initial,
          RankRegularControlledChain.nil initial, hterminal⟩
      · have hs_le : initial.density ≤ t.density := by
          calc
            initial.density = 1 * initial.density := by ring
            _ ≤ q * initial.density :=
              mul_le_mul_of_nonneg_right hq initial.density_nonneg
            _ ≤ t.density := hst.1
        have hscale' : lower ≤ t.density := hscale.trans hs_le
        have hrank' : t.rank ≤ (used + 1) * rankCost := by
          calc
            t.rank ≤ initial.rank + rankCost := hst.2.1
            _ ≤ used * rankCost + rankCost :=
              Nat.add_le_add_right hrank rankCost
            _ = (used + 1) * rankCost := by
              rw [Nat.add_mul]
              simp
        have hbudget' : used + 1 + remaining ≤ total := by omega
        have hqpow : 0 ≤ q ^ remaining := pow_nonneg (zero_le_one.trans hq) _
        have hgrowth' : 1 < q ^ remaining * t.density := by
          calc
            1 < q ^ (remaining + 1) * initial.density := by simpa using hgrowth
            _ = q ^ remaining * (q * initial.density) := by
              rw [pow_succ]
              ring
            _ ≤ q ^ remaining * t.density :=
              mul_le_mul_of_nonneg_left hst.1 hqpow
        obtain ⟨n, hn, u, hchain, hu⟩ :=
          ih hbudget' t hscale' hrank' hgrowth'
        exact ⟨n + 1, by omega, u,
          RankRegularControlledChain.cons hst hchain, hu⟩

/-- Dyadic scale for the honest cyclic initial rank-regular state. -/
theorem cyclicInitialRankRegular_onDyadicScale
    {N d : ℕ} (hN : 1 ≤ N)
    {A : Finset (ZMod (intervalModulus N))} (hA : A.Nonempty)
    (hlog : Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
      (d : ℝ) * Real.log 2) :
    BohrStopping.OnDyadicScale d
      (cyclicInitialRankRegularLocated N A hA).density := by
  have hmodNat : 0 < intervalModulus N := by simp [intervalModulus]
  have hmod : (0 : ℝ) < intervalModulus N := by exact_mod_cast hmodNat
  have hcard : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
  have hratio : (0 : ℝ) <
      ((intervalModulus N : ℕ) : ℝ) / (#A : ℝ) := div_pos hmod hcard
  have hpow : (0 : ℝ) < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  have hlog' :
      Real.log (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤
        Real.log ((2 : ℝ) ^ d) := by
    simpa [Real.log_pow] using hlog
  have hratio_le :
      (((intervalModulus N : ℕ) : ℝ) / (#A : ℝ)) ≤ (2 : ℝ) ^ d :=
    (Real.log_le_log_iff hratio hpow).mp hlog'
  have hmul : (((intervalModulus N : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ d * (#A : ℝ) := (div_le_iff₀ hcard).mp hratio_le
  rw [BohrStopping.OnDyadicScale]
  simp only [cyclicInitialRankRegularLocated_density]
  apply (div_le_div_iff₀ hpow hmod).2
  simpa [mul_comm] using hmul

/-- Quantitative analytic supply required by the rank-regular recursion.
The used-step index exposes exactly the dyadic density and accumulated rank
bounds available to the concrete construction. -/
def RawConcreteSupply (K : ℝ) : Prop :=
  ∀ (N : ℕ),
    ∀ (A : Finset (ZMod (intervalModulus N))), A.Nonempty →
      ∀ d : ℕ, 1 ≤ d →
        ∃ rankCost p : ℕ, 0 < p ∧
          ∀ n < 1024 * (d + 1),
            ∀ s : RankRegularLocatedRestriction A,
              (1 / (2 : ℝ) ^ d) ≤ s.density →
              s.rank ≤ n * rankCost →
              ∃ P : RankRegularNarrowingPackage s (1 / 512 : ℝ)
                (K * ((d + 1 : ℕ) : ℝ) ^ 11) rankCost,
                ∀ hdense : DensityStep.HasDensePair s.located
                    P.childOne P.childTwo (1 / 512 : ℝ),
                  Nonempty (RawTwoBohrEndpointPackage (p := p) s P hdense)

/-- The concrete rank-regular supply gives the full cyclic Holder
certificate hypothesis without passing through a generic non-regular
maximal-state interface. -/
theorem holderCertificates_of_rawConcreteSupply
    {K : ℝ} (hK : 0 < K) (hsupply : RawConcreteSupply K) :
    KelleyMekaHolderCertificateHypothesis
      (8 + 2050 * (2 : ℝ) ^ 12 * K) := by
  refine ⟨by positivity, ?_⟩
  intro N hN A hA d hd hlog
  obtain ⟨rankCost, p, hp, hlocal⟩ := hsupply N A hA d hd
  let fuel : ℕ := 1024 * (d + 1)
  let initial := cyclicInitialRankRegularLocated N A hA
  let Terminal : RankRegularLocatedRestriction A → Prop :=
    fun s => Nonempty (LocatedHolderTerminalData s.located K d)
  have hstep : ∀ n < fuel, ∀ s : RankRegularLocatedRestriction A,
      (1 / (2 : ℝ) ^ d) ≤ s.density →
      s.rank ≤ n * rankCost →
      Terminal s ∨ ∃ t : RankRegularLocatedRestriction A,
        BohrStopping.IsControlledIncrement (1025 / 1024 : ℝ) rankCost
          (K * ((d + 1 : ℕ) : ℝ) ^ 11)
          s.located.restriction t.located.restriction := by
    intro n hn s hscale hrank
    obtain ⟨P, hendpoint⟩ := hlocal n (by simpa [fuel] using hn) s hscale hrank
    exact terminalData_or_rankRegular_increment s P hp hendpoint
  have hdyadic := cyclicInitialRankRegular_onDyadicScale hN hA hlog
  have hscaleInitial :
      (1 / (2 : ℝ) ^ d) ≤ initial.density := by
    change (1 / (2 : ℝ) ^ d) ≤ (cyclicInitialLocated N A hA).density
    exact hdyadic
  have hgrowth :
      1 < (1025 / 1024 : ℝ) ^ fuel * initial.density := by
    simpa [fuel, initial] using
      fixedIncrement_growth_of_dyadicScale
        (cyclicInitialLocated N A hA) hdyadic
  obtain ⟨n, hn, t, hchain, hterminal⟩ :=
    exists_terminal_rankRegular_chain_bounded_aux
      (Terminal := Terminal) (q := (1025 / 1024 : ℝ))
      (lower := 1 / (2 : ℝ) ^ d)
      (sizeCost := K * ((d + 1 : ℕ) : ℝ) ^ 11)
      (rankCost := rankCost) (total := fuel) (used := 0)
      (remaining := fuel) (by norm_num) (by omega) hstep initial
      hscaleInitial (by simp [initial]) hgrowth
  let data := Classical.choice hterminal
  have hforget := hchain.forget
  have hdensity0 :=
    hforget.density_bound (by norm_num)
  change (1025 / 1024 : ℝ) ^ n *
      (cyclicInitialLocated N A hA).density ≤ t.located.density at hdensity0
  have hdensity :
      (1025 / 1024 : ℝ) ^ n *
          (cyclicInitialLocated N A hA).density ≤ t.located.density := by
    exact hdensity0
  have hcard0 := hforget.card_bound
  change Real.exp (-(n : ℝ) * (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
      ((cyclicInitialLocated N A hA).card : ℝ) ≤ t.located.card at hcard0
  have hcard :
      Real.exp (-(n : ℝ) * (K * ((d + 1 : ℕ) : ℝ) ^ 11)) *
          ((cyclicInitialLocated N A hA).card : ℝ) ≤ t.located.card := by
    exact hcard0
  exact ⟨CyclicHolderCertificate.of_locatedTerminalData hd hA hK.le hn
    hdyadic hdensity hcard data⟩

end

end FinalAssembly

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/BohrScaleVolume.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

/-!
# Arbitrary-scale finite Bohr volume comparison

The four-cell argument in BourgainRegular is convenient at the fixed
scales 1 and 1 / 2. Here we record the same finite signature/fibre
argument at an arbitrary positive integral resolution.

For one coordinate of width w, the interval [-w,w] is split into
2m + 1 consecutive cells of diameter at most w / m. Equal signatures
therefore inject into the carrier at scale rho / m. The resulting bound
has no regularity, positivity-of-width, or ambient-size hypothesis:

|B_rho| <= (2m + 1)^rank(B) |B_(rho/m)|.

For later bookkeeping we also expose the cleaner, slightly weaker
(3m)^rank form, together with its real-valued exponential rewriting.
-/

open _root_.Finset
open scoped BigOperators _root_.NNReal

noncomputable section

namespace BohrData

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Scaled interval cells -/

/-- A total coding of a real coordinate into 2m + 1 cells. On the interval
[-w,w] with 0 < w, the unclamped value is floor ((r+w)m/w); the outer min
only makes the definition total away from that interval. -/
def scaledCell (m : ℕ) (w r : ℝ) : Fin (2 * m + 1) :=
  ⟨min ⌊((r + w) * (m : ℝ)) / w⌋₊ (2 * m),
    Nat.lt_succ_iff.mpr (Nat.min_le_right _ _)⟩

/-- Points of [-w,w] in the same scaled cell are at distance at most
w / m. The case w = 0 is included, so no hidden positivity assumption
on Bohr widths is needed later. -/
lemma abs_sub_le_div_of_scaledCell_eq
    {m : ℕ} (hm : 0 < m) {w r s : ℝ}
    (hw : 0 ≤ w) (hr : |r| ≤ w) (hs : |s| ≤ w)
    (hcell : scaledCell m w r = scaledCell m w s) :
    |r - s| ≤ w / (m : ℝ) := by
  by_cases hw0 : w = 0
  · subst w
    have hr0 : r = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm hr (abs_nonneg r)
    have hs0 : s = 0 := by
      apply abs_eq_zero.mp
      exact le_antisymm hs (abs_nonneg s)
    simp [hr0, hs0]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let ur : ℝ := ((r + w) * (m : ℝ)) / w
  let us : ℝ := ((s + w) * (m : ℝ)) / w
  have hr_bounds : -w ≤ r ∧ r ≤ w := (abs_le.mp hr)
  have hs_bounds : -w ≤ s ∧ s ≤ w := (abs_le.mp hs)
  have hur0 : 0 ≤ ur := by
    dsimp [ur]
    exact div_nonneg (mul_nonneg (by linarith) hmR.le) hw
  have hus0 : 0 ≤ us := by
    dsimp [us]
    exact div_nonneg (mul_nonneg (by linarith) hmR.le) hw
  have hur_le : ur ≤ (2 * m : ℕ) := by
    dsimp [ur]
    apply (div_le_iff₀ hwpos).2
    push_cast
    nlinarith
  have hus_le : us ≤ (2 * m : ℕ) := by
    dsimp [us]
    apply (div_le_iff₀ hwpos).2
    push_cast
    nlinarith
  have hfloor_r_lt : ⌊ur⌋₊ < 2 * m + 1 := by
    apply (Nat.floor_lt hur0).2
    exact lt_of_le_of_lt hur_le (by exact_mod_cast (Nat.lt_succ_self (2 * m)))
  have hfloor_s_lt : ⌊us⌋₊ < 2 * m + 1 := by
    apply (Nat.floor_lt hus0).2
    exact lt_of_le_of_lt hus_le (by exact_mod_cast (Nat.lt_succ_self (2 * m)))
  have hfloor_r_le : ⌊ur⌋₊ ≤ 2 * m := by omega
  have hfloor_s_le : ⌊us⌋₊ ≤ 2 * m := by omega
  have hfloor : ⌊ur⌋₊ = ⌊us⌋₊ := by
    have hval := congrArg Fin.val hcell
    simpa only [scaledCell, ur, us, Nat.min_eq_left hfloor_r_le,
      Nat.min_eq_left hfloor_s_le] using hval
  have hur_lower : ((⌊ur⌋₊ : ℕ) : ℝ) ≤ ur := Nat.floor_le hur0
  have hur_upper : ur < ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one ur
  have hus_lower : ((⌊us⌋₊ : ℕ) : ℝ) ≤ us := Nat.floor_le hus0
  have hus_upper : us < ((⌊us⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one us
  have hur_lt_us_add : ur < us + 1 := by
    calc
      ur < ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := hur_upper
      _ = ((⌊us⌋₊ : ℕ) : ℝ) + 1 := by rw [hfloor]
      _ ≤ us + 1 := by gcongr
  have hus_lt_ur_add : us < ur + 1 := by
    calc
      us < ((⌊us⌋₊ : ℕ) : ℝ) + 1 := hus_upper
      _ = ((⌊ur⌋₊ : ℕ) : ℝ) + 1 := by rw [← hfloor]
      _ ≤ ur + 1 := by gcongr
  have hur_sub_us :
      ur - us = ((r - s) * (m : ℝ)) / w := by
    dsimp [ur, us]
    field_simp
    ring
  have hquot_upper : ((r - s) * (m : ℝ)) / w < 1 := by
    rw [← hur_sub_us]
    linarith
  have hquot_lower : (-1 : ℝ) < ((r - s) * (m : ℝ)) / w := by
    rw [← hur_sub_us]
    linarith
  have hmul_upper : (r - s) * (m : ℝ) < w := by
    have h := (div_lt_iff₀ hwpos).mp hquot_upper
    simpa only [one_mul] using h
  have hmul_lower : -w < (r - s) * (m : ℝ) := by
    have h := (lt_div_iff₀ hwpos).mp hquot_lower
    simpa only [neg_one_mul] using h
  have hupper : r - s < w / (m : ℝ) :=
    (lt_div_iff₀ hmR).2 hmul_upper
  have hlower : -(w / (m : ℝ)) < r - s := by
    have h := (div_lt_iff₀ hmR).2 hmul_lower
    simpa only [neg_div] using h
  exact (abs_lt.2 ⟨hlower, hupper⟩).le

/-- The scaled-cell signature of a point in the rho-dilate. -/
def scaledSignature (B : BohrData G) (rho : NNReal) (m : ℕ)
    (x : ↥(B.dilate rho).carrier) : B.freq → Fin (2 * m + 1) :=
  fun γ ↦
    scaledCell m ((rho : ℝ) * (B.width γ.1 : ℝ))
      (circleRep (γ.1 x.1))

private lemma sub_mem_dilate_div_of_scaledSignature_eq
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m)
    {x y : ↥(B.dilate rho).carrier}
    (hxy : B.scaledSignature rho m x = B.scaledSignature rho m y) :
    x.1 - y.1 ∈ (B.dilate (rho / (m : NNReal))).carrier := by
  rw [mem_carrier]
  intro γ hγ
  have hx := (mem_carrier (B.dilate rho) x.1).mp x.2 γ hγ
  have hy := (mem_carrier (B.dilate rho) y.1).mp y.2 γ hγ
  simp only [width_dilate, NNReal.coe_mul] at hx hy ⊢
  rw [map_sub]
  have hxrep :
      |circleRep (γ x.1)| ≤ (rho : ℝ) * (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hyrep :
      |circleRep (γ y.1)| ≤ (rho : ℝ) * (B.width γ : ℝ) := by
    rwa [← norm_eq_abs_circleRep]
  have hcoord := congrFun hxy ⟨γ, hγ⟩
  have hdiv := abs_sub_le_div_of_scaledCell_eq hm
    (mul_nonneg (by positivity) (by positivity)) hxrep hyrep hcoord
  calc
    ‖γ x.1 - γ y.1‖ ≤
        |circleRep (γ x.1) - circleRep (γ y.1)| :=
      norm_sub_le_abs_circleRep_sub _ _
    _ ≤ ((rho : ℝ) * (B.width γ : ℝ)) / (m : ℝ) := hdiv
    _ = ((rho / (m : NNReal) : NNReal) : ℝ) *
        (B.width γ : ℝ) := by
      push_cast
      field_simp

private lemma card_scaledSignature_fiber_le
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m)
    (a : B.freq → Fin (2 * m + 1)) :
    Fintype.card
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} ≤
      (B.dilate (rho / (m : NNReal))).carrier.card := by
  classical
  by_cases hfiber : Nonempty
      {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a}
  · let x₀ :
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} :=
      Classical.choice hfiber
    let f :
        {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} →
          ↥(B.dilate (rho / (m : NNReal))).carrier :=
      fun x ↦
        ⟨x.1.1 - x₀.1.1,
          sub_mem_dilate_div_of_scaledSignature_eq B rho hm
            (x.2.trans x₀.2.symm)⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      dsimp [f] at hval
      exact sub_left_injective hval
    calc
      Fintype.card
          {x : ↥(B.dilate rho).carrier // B.scaledSignature rho m x = a} ≤
          Fintype.card ↥(B.dilate (rho / (m : NNReal))).carrier :=
        Fintype.card_le_of_injective f hf
      _ = (B.dilate (rho / (m : NNReal))).carrier.card :=
        Fintype.card_coe _
  · simp only [not_nonempty_iff] at hfiber
    simp

/-! ## Volume comparison -/

/-- Arbitrary-scale relative volume growth for a finite Bohr carrier.
Shrinking a scale by a positive integer m costs at most
(2m+1)^rank. -/
theorem card_dilate_le_two_mul_add_one_pow_rank_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    (B.dilate rho).carrier.card ≤
      (2 * m + 1) ^ B.rank *
        (B.dilate (rho / (m : NNReal))).carrier.card := by
  classical
  let S := B.freq → Fin (2 * m + 1)
  let q : ↥(B.dilate rho).carrier → S := B.scaledSignature rho m
  have hfiber : ∀ a : S,
      Fintype.card {x : ↥(B.dilate rho).carrier // q x = a} ≤
        (B.dilate (rho / (m : NNReal))).carrier.card := by
    intro a
    exact card_scaledSignature_fiber_le B rho hm a
  have hcardS : Fintype.card S = (2 * m + 1) ^ B.rank := by
    dsimp [S, rank]
    rw [Fintype.card_pi]
    simp
  rw [← Fintype.card_coe (B.dilate rho).carrier, ← hcardS]
  by_contra h
  have hlt :
      Fintype.card S * (B.dilate (rho / (m : NNReal))).carrier.card <
        Fintype.card ↥(B.dilate rho).carrier := by omega
  obtain ⟨a, ha⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := q) hlt
  have hfa : #{x | q x = a} ≤
      (B.dilate (rho / (m : NNReal))).carrier.card := by
    rw [← Fintype.card_subtype]
    exact hfiber a
  exact (not_lt_of_ge hfa) ha

/-- A cleaner bookkeeping form of the arbitrary-scale volume estimate. -/
theorem card_dilate_le_three_mul_pow_rank_mul_card_div
    (B : BohrData G) (rho : NNReal) {m : ℕ} (hm : 0 < m) :
    (B.dilate rho).carrier.card ≤
      (3 * m) ^ B.rank *
        (B.dilate (rho / (m : NNReal))).carrier.card := by
  calc
    (B.dilate rho).carrier.card ≤
        (2 * m + 1) ^ B.rank *
          (B.dilate (rho / (m : NNReal))).carrier.card :=
      card_dilate_le_two_mul_add_one_pow_rank_mul_card_div B rho hm
    _ ≤ (3 * m) ^ B.rank *
          (B.dilate (rho / (m : NNReal))).carrier.card := by
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_left
      omega

end BohrData

end

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/TwoBohrBalanced.lean` -/

section
/-!
# Balanced restriction with two Bohr geometries

The balanced function is formed relative to a baseline rank-regular Bohr
carrier `K`, because that is the carrier containing `A` and hence the one
whose reciprocal cardinality is the main term in localized unbalancing.
The convolution-comparison norm, however, may be taken on a second
rank-regular Bohr carrier `W`.  The same smoothing sets `D,E` are assumed
small for the geometry of `W`, while their autocorrelation weight is assumed
supported in the narrow dilate of `K` required by localized unbalancing.

This is the form needed downstream when the uniform norm and the density
baseline live on different regular Bohr sets.
-/

open _root_.Finset Fintype _root_.Function _root_.MeasureTheory _root_.RCLike _root_.Real
open scoped BigOperators ComplexConjugate ComplexOrder _root_.ENNReal _root_.NNReal Pointwise

namespace TwoBohrBalanced

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

end
end TwoBohrBalanced

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/HolderApproximation.lean` -/

section
/-!
# The rank-regular Hölder approximation

This file isolates the last boundary calculation in the local Hölder step.
The function is written explicitly, rather than through the final assembly
alias, so that this module can be imported by that assembly without a cycle.
-/

open _root_.Finset Fintype _root_.Function
open scoped BigOperators _root_.NNReal

namespace HolderApproximation

noncomputable section

variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

private lemma normalizedIndicator_neg_eq (K : BohrData G) (x : G) :
    normalizedIndicator K.carrier (-x) = normalizedIndicator K.carrier x := by
  by_cases hx : x ∈ K.carrier
  · have hnx : -x ∈ K.carrier := BohrData.neg_mem_carrier.mpr hx
    simp [normalizedIndicator_apply_mem hx, normalizedIndicator_apply_mem hnx]
  · have hnx : -x ∉ K.carrier := by
      intro h
      exact hx (BohrData.neg_mem_carrier.mp h)
    simp [normalizedIndicator_apply_not_mem hx,
      normalizedIndicator_apply_not_mem hnx]

/-- A point of a small Bohr dilate sees the mixed `A*K` convolution as the
constant density `1/|K|`, with the rank-regular boundary error amplified only
by `1/|A|`. -/
theorem abs_normalizedConvolution_subset_carrier_sub_inv_le
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    {t : G} (ht : t ∈ (K.dilate κ).carrier) :
    |normalizedConvolution (normalizedIndicator A)
        (normalizedIndicator K.carrier) t - (K.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) := by
  let E : ℝ := 200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hAcard : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
  have hsumA : ∑ x : G, normalizedIndicator A x = 1 :=
    sum_normalizedIndicator hA
  have hbase :
      ∑ x : G, normalizedIndicator A x * (K.carrier.card : ℝ)⁻¹ =
        (K.carrier.card : ℝ)⁻¹ := by
    rw [← Finset.sum_mul, hsumA, one_mul]
  have hsumDiff :
      ∑ x : G,
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| ≤ E := by
    have hneg : -t ∈ (K.dilate κ).carrier :=
      BohrData.neg_mem_carrier.mpr ht
    have htranslate :=
      BohrData.sum_abs_normalizedIndicator_translate_le_of_rankRegular
        hreg hκ hneg
    calc
      ∑ x : G,
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| =
          ∑ x : G,
            |normalizedIndicator K.carrier (x - -t) -
              normalizedIndicator K.carrier x| := by
        refine Fintype.sum_equiv (Equiv.neg G) _ _ ?_
        intro x
        simp only [Equiv.neg_apply]
        congr 2 <;> abel
      _ ≤ E := htranslate
  have hweighted :
      ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| ≤
        (A.card : ℝ)⁻¹ * E := by
    calc
      ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| =
          (A.card : ℝ)⁻¹ * ∑ x ∈ A,
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)| := by
        change (∑ x : G, (if x ∈ A then (A.card : ℝ)⁻¹ else 0) *
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)|) = _
        simp only [ite_mul, zero_mul]
        rw [← Finset.sum_filter]
        have hfilter : (Finset.univ : Finset G).filter (fun x ↦ x ∈ A) = A := by
          ext x
          simp
        rw [hfilter, Finset.mul_sum]
      _ ≤ (A.card : ℝ)⁻¹ * ∑ x : G,
            |normalizedIndicator K.carrier (t - x) -
              normalizedIndicator K.carrier (-x)| := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun _ _ _ ↦ abs_nonneg _)
        · positivity
      _ ≤ (A.card : ℝ)⁻¹ * E :=
        mul_le_mul_of_nonneg_left hsumDiff (by positivity)
  rw [normalizedConvolution, ← hbase, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    |∑ x : G, normalizedIndicator A x *
        (normalizedIndicator K.carrier (t - x) -
          (K.carrier.card : ℝ)⁻¹)| =
        |∑ x : G, normalizedIndicator A x *
          (normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x))| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A
      · rw [normalizedIndicator_neg_eq K x,
          normalizedIndicator_apply_mem (hAK hx)]
      · simp [normalizedIndicator_apply_not_mem hx]
    _ ≤ ∑ x : G, |normalizedIndicator A x *
          (normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x))| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ x : G, normalizedIndicator A x *
          |normalizedIndicator K.carrier (t - x) -
            normalizedIndicator K.carrier (-x)| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (normalizedIndicator_nonneg A x)]
    _ ≤ (A.card : ℝ)⁻¹ * E := hweighted

private lemma localAverage_sub_const
    {C : Finset G} (hC : C.Nonempty) (f : G → ℝ) (c : ℝ) :
    HolderLifting.localAverage C f - c =
      HolderLifting.localAverage C (fun x ↦ f x - c) := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hCcard : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
  field_simp

private lemma localAverage_const
    {C : Finset G} (hC : C.Nonempty) (c : ℝ) :
    HolderLifting.localAverage C (fun _ ↦ c) = c := by
  unfold HolderLifting.localAverage
  simp [hC.card_ne_zero]

/-- Averaging the preceding pointwise estimate over a nonempty set of small
translations preserves its right-hand side. -/
theorem abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A C : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hC : C.Nonempty) (hCsmall : C ⊆ (K.dilate κ).carrier) :
    |HolderLifting.localAverage C
        (normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier)) - (K.carrier.card : ℝ)⁻¹| ≤
      (A.card : ℝ)⁻¹ *
        (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) := by
  let M : ℝ := (A.card : ℝ)⁻¹ *
    (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))
  rw [localAverage_sub_const hC]
  calc
    |HolderLifting.localAverage C (fun x ↦
        normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier) x - (K.carrier.card : ℝ)⁻¹)| ≤
      HolderLifting.localAverage C (fun x ↦
        |normalizedConvolution (normalizedIndicator A)
          (normalizedIndicator K.carrier) x - (K.carrier.card : ℝ)⁻¹|) :=
      HolderLifting.abs_localAverage_le_localAverage_abs _
    _ ≤ HolderLifting.localAverage C (fun _ ↦ M) := by
      unfold HolderLifting.localAverage
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro x hx
        exact abs_normalizedConvolution_subset_carrier_sub_inv_le
          hreg hκ hA hAK (hCsmall hx)
      · positivity
    _ = M := localAverage_const hC M

private lemma normalizedConvolution_sub_sub_apply
    (a k : G → ℝ) (x : G) :
    normalizedConvolution (a - k) (a - k) x =
      normalizedConvolution a a x - normalizedConvolution a k x -
        normalizedConvolution k a x + normalizedConvolution k k x := by
  unfold normalizedConvolution
  simp only [Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

private lemma localAverage_add
    {C : Finset G} (f g : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ f x + g x) =
      HolderLifting.localAverage C f + HolderLifting.localAverage C g := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_add_distrib, add_div]

private lemma localAverage_sub
    {C : Finset G} (f g : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ f x - g x) =
      HolderLifting.localAverage C f - HolderLifting.localAverage C g := by
  unfold HolderLifting.localAverage
  rw [Finset.sum_sub_distrib, sub_div]

private lemma localAverage_mul_const_left
    {C : Finset G} (c : ℝ) (f : G → ℝ) :
    HolderLifting.localAverage C (fun x ↦ c * f x) =
      c * HolderLifting.localAverage C f := by
  unfold HolderLifting.localAverage
  rw [← Finset.mul_sum]
  ring

/-- The concrete three-term Holder approximation.  `C` is the doubled
middle-term set in the endpoint application; the statement is kept at this
level so it can be reused without importing the final assembly namespace. -/
theorem normalizedMixedProgression_scaledBalanced_approximation
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A A'' : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hA'' : A''.Nonempty)
    (hCsmall : GroupCount.doubledFinset A'' ⊆ (K.dilate κ).carrier)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        ((K.carrier.card : ℝ)⁻¹) / 8) :
    |(GroupCount.normalizedMixedProgression A A'' -
        (Fintype.card G : ℝ) / (#K.carrier : ℝ)) -
        HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (normalizedIndicator A - normalizedIndicator K.carrier)
              (normalizedIndicator A - normalizedIndicator K.carrier))
          (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
  let C := GroupCount.doubledFinset A''
  let gAA := normalizedConvolution (normalizedIndicator A) (normalizedIndicator A)
  let gAK := normalizedConvolution (normalizedIndicator A) (normalizedIndicator K.carrier)
  let gKA := normalizedConvolution (normalizedIndicator K.carrier) (normalizedIndicator A)
  let gKK := normalizedConvolution (normalizedIndicator K.carrier) (normalizedIndicator K.carrier)
  let invK : ℝ := (K.carrier.card : ℝ)⁻¹
  let E : ℝ := 200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)
  have hC : C.Nonempty := GroupCount.doubledFinset_nonempty hA''
  have hAKavg : |HolderLifting.localAverage C gAK - invK| ≤
      (A.card : ℝ)⁻¹ * E := by
    simpa [C, gAK, invK, E] using
      abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
        hreg hκ hA hAK hC hCsmall
  have hKAavg : |HolderLifting.localAverage C gKA - invK| ≤
      (A.card : ℝ)⁻¹ * E := by
    rw [show gKA = gAK by
      dsimp [gKA, gAK]
      exact normalizedConvolution_comm _ _]
    exact hAKavg
  have hKKavg : |HolderLifting.localAverage C gKK - invK| ≤ invK * E := by
    simpa [C, gKK, invK, E] using
      abs_localAverage_normalizedConvolution_subset_carrier_sub_inv_le
        hreg hκ K.carrier_nonempty (Finset.Subset.rfl) hC hCsmall
  have hsum :
      |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| ≤
        2 * ((A.card : ℝ)⁻¹ * E) + invK * E := by
    calc
      |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| ≤
        |HolderLifting.localAverage C gAK - invK| +
          |HolderLifting.localAverage C gKA - invK| +
          |HolderLifting.localAverage C gKK - invK| := by
        calc
          |_ - _| ≤ |(HolderLifting.localAverage C gAK - invK) +
              (HolderLifting.localAverage C gKA - invK)| +
              |HolderLifting.localAverage C gKK - invK| := by
            simpa [abs_sub_comm] using (abs_sub_le
              ((HolderLifting.localAverage C gAK - invK) +
                (HolderLifting.localAverage C gKA - invK))
              (0 : ℝ) (HolderLifting.localAverage C gKK - invK))
          _ ≤ (|HolderLifting.localAverage C gAK - invK| +
              |HolderLifting.localAverage C gKA - invK|) +
              |HolderLifting.localAverage C gKK - invK| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 2 * ((A.card : ℝ)⁻¹ * E) + invK * E := by
        nlinarith
  have hmain : (Fintype.card G : ℝ) / (#K.carrier : ℝ) =
      (Fintype.card G : ℝ) * invK := by
    simp [invK, div_eq_mul_inv]
  have hprog : GroupCount.normalizedMixedProgression A A'' =
      (Fintype.card G : ℝ) * HolderLifting.localAverage C gAA := by
    rw [GroupCount.normalizedMixedProgression_eq_localAverage hA'']
    change HolderLifting.localAverage C
        (fun x ↦ (Fintype.card G : ℝ) * gAA x) = _
    rw [localAverage_mul_const_left]
  have hpair :
      HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (normalizedIndicator A - normalizedIndicator K.carrier)
              (normalizedIndicator A - normalizedIndicator K.carrier)) C =
        (Fintype.card G : ℝ) *
          (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
            HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK) := by
    rw [HolderLifting.pairing_eq_localAverage hC]
    change HolderLifting.localAverage C (fun x ↦ (Fintype.card G : ℝ) *
      normalizedConvolution
        (normalizedIndicator A - normalizedIndicator K.carrier)
        (normalizedIndicator A - normalizedIndicator K.carrier) x) = _
    rw [localAverage_mul_const_left]
    congr 1
    rw [show normalizedConvolution
        (normalizedIndicator A - normalizedIndicator K.carrier)
        (normalizedIndicator A - normalizedIndicator K.carrier) =
        (fun x ↦ gAA x - gAK x - gKA x + gKK x) by
      funext x
      simpa [gAA, gAK, gKA, gKK] using
        normalizedConvolution_sub_sub_apply (normalizedIndicator A)
          (normalizedIndicator K.carrier) x]
    rw [localAverage_add, localAverage_sub, localAverage_sub]
  rw [hprog, hmain, hpair]
  have hcardG : 0 ≤ (Fintype.card G : ℝ) := by positivity
  calc
    |((Fintype.card G : ℝ) * HolderLifting.localAverage C gAA -
        (Fintype.card G : ℝ) * invK) -
        (Fintype.card G : ℝ) *
          (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
            HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK)| =
      (Fintype.card G : ℝ) *
        |(HolderLifting.localAverage C gAK - invK) +
          (HolderLifting.localAverage C gKA - invK) -
          (HolderLifting.localAverage C gKK - invK)| := by
      have heq :
          (Fintype.card G : ℝ) * HolderLifting.localAverage C gAA -
              (Fintype.card G : ℝ) * invK -
              (Fintype.card G : ℝ) *
                (HolderLifting.localAverage C gAA - HolderLifting.localAverage C gAK -
                  HolderLifting.localAverage C gKA + HolderLifting.localAverage C gKK) =
            (Fintype.card G : ℝ) *
              ((HolderLifting.localAverage C gAK - invK) +
                (HolderLifting.localAverage C gKA - invK) -
                (HolderLifting.localAverage C gKK - invK)) := by ring
      rw [heq, abs_mul, abs_of_nonneg hcardG]
    _ ≤ (Fintype.card G : ℝ) *
        (2 * ((A.card : ℝ)⁻¹ * E) + invK * E) :=
      mul_le_mul_of_nonneg_left hsum hcardG
    _ ≤ (Fintype.card G : ℝ) * (invK / 8) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [E, invK] using hwidth
      · exact hcardG
    _ = ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
      rw [hmain]
      ring

/-- Endpoint-shaped form of the approximation.  This is the version consumed
by `RawTwoBohrEndpointPackage`: its stored boundary budget is the stronger
`(1/8)/8` budget, and APAP's `μ` notation is used for the balanced function. -/
theorem normalizedMixedProgression_scaledBalanced_approximation_of_boundaryWidth
    {K : BohrData G} (hreg : K.IsRankRegular) {κ : ℝ≥0}
    (hκ : κ ≤ 1 / (100 * (max K.rank 1 : ℕ) : ℝ≥0))
    {A A'' : Finset G} (hA : A.Nonempty) (hAK : A ⊆ K.carrier)
    (hA'' : A''.Nonempty)
    (hCsmall : GroupCount.doubledFinset A'' ⊆ (K.dilate κ).carrier)
    (hwidth :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (K.carrier.card : ℝ)⁻¹) :
    |(GroupCount.normalizedMixedProgression A A'' -
        (Fintype.card G : ℝ) / (#K.carrier : ℝ)) -
        HolderLifting.pairing
          ((Fintype.card G : ℝ) •
            normalizedConvolution
              (μ_[ℝ] A - μ K.carrier)
              (μ A - μ K.carrier))
          (GroupCount.doubledFinset A'')| ≤
      ((Fintype.card G : ℝ) / (#K.carrier : ℝ)) / 8 := by
  have hKinv : 0 ≤ (K.carrier.card : ℝ)⁻¹ := by positivity
  have hwidth' :
      2 * ((A.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ))) +
        (K.carrier.card : ℝ)⁻¹ *
          (200 * ((max K.rank 1 : ℕ) : ℝ) * (κ : ℝ)) ≤
        ((K.carrier.card : ℝ)⁻¹) / 8 := by
    apply hwidth.trans
    nlinarith
  have hmuA : μ_[ℝ] A = normalizedIndicator A :=
    LocalizedUnbalancing.mu_eq_normalizedIndicator A
  have hmuK : μ_[ℝ] K.carrier = normalizedIndicator K.carrier :=
    LocalizedUnbalancing.mu_eq_normalizedIndicator K.carrier
  simpa only [hmuA, hmuK] using
    normalizedMixedProgression_scaledBalanced_approximation hreg hκ hA hAK
      hA'' hCsmall hwidth'

end
end HolderApproximation

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/ConcreteNumerics.lean` -/

section
/-!
# Stable numerical choices for the concrete supply

The final analytic supply still chooses its rank budget from the local
Chang dimension. Once that positive budget is fixed, the two reciprocal
Bohr-child denominators below are uniform in every state whose rank is at
most the accumulated 1024 times d-plus-one budget.
-/

open _root_.Finset
open scoped _root_.NNReal

namespace ConcreteNumerics

noncomputable section

/-- Uniform upper bound for the rank of a state after at most
1024 times d-plus-one steps. -/
def rankCap (d rankCost : ℕ) : ℕ :=
  1024 * (d + 1) * rankCost

/-- Reciprocal denominator for the first Bourgain child. The factor
819200 = 400 * 2048 pays simultaneously for rank regularity and the
epsilonDense = 1/512 narrowing inequality. -/
def mOne (d rankCost : ℕ) : ℕ :=
  819200 * rankCap d rankCost * 2 ^ d

/-- Reciprocal denominator for the second, Holder-small child. Its
coefficient is deliberately coarse and leaves room for the endpoint-density
loss used by the boundary-width estimate. -/
def mTwo (d rankCost : ℕ) : ℕ :=
  76800 * rankCap d rankCost * 2 ^ (d + 1)

lemma rankCap_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < rankCap d rankCost := by
  unfold rankCap
  positivity

lemma one_le_rankCap {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    1 ≤ rankCap d rankCost :=
  Nat.one_le_iff_ne_zero.mpr (rankCap_pos hrankCost).ne'

lemma max_rank_le_rankCap {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    max r 1 ≤ rankCap d rankCost := by
  exact max_le hrank (one_le_rankCap hrankCost)

lemma mOne_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < mOne d rankCost := by
  unfold mOne
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (rankCap_pos hrankCost))
    (pow_pos (by norm_num) _)

lemma mTwo_pos {d rankCost : ℕ} (hrankCost : 0 < rankCost) :
    0 < mTwo d rankCost := by
  unfold mTwo
  exact Nat.mul_pos
    (Nat.mul_pos (by norm_num) (rankCap_pos hrankCost))
    (pow_pos (by norm_num) _)

/-- The first denominator is certainly at least 100 times rank, as needed
for rank-regular Bohr estimates. -/
lemma hundred_mul_max_rank_le_mOne {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    100 * max r 1 ≤ mOne d rankCost := by
  have hmax := max_rank_le_rankCap hrankCost hrank
  unfold mOne
  calc
    100 * max r 1 ≤ 100 * rankCap d rankCost :=
      Nat.mul_le_mul_left 100 hmax
    _ ≤ 819200 * rankCap d rankCost * 2 ^ d := by
      have hcoeff : 100 ≤ 819200 := by omega
      calc
        100 * rankCap d rankCost ≤ 819200 * rankCap d rankCost :=
          Nat.mul_le_mul_right _ hcoeff
        _ ≤ 819200 * rankCap d rankCost * 2 ^ d :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)

/-- Concrete first-scale rank condition in the exact NNReal shape used by
ReciprocalStepBounds.scale_rank. -/
lemma inv_mOne_le_rank_scale {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    ((mOne d rankCost : NNReal)⁻¹) ≤
      1 / (100 * (max r 1 : ℕ) : NNReal) := by
  rw [one_div]
  have hleft : (0 : NNReal) < mOne d rankCost := by
    exact_mod_cast mOne_pos hrankCost
  have hright : (0 : NNReal) < 100 * (max r 1 : ℕ) := by
    positivity
  apply (inv_le_inv₀ hleft hright).2
  exact_mod_cast hundred_mul_max_rank_le_mOne hrankCost hrank

/-- The same first denominator also discharges the exact density-narrowing
scale inequality at epsilonDense = 1/512 on a dyadic density state. -/
lemma mOne_scale_density {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost)
    {density : ℝ}
    (hdensity : 1 / (2 : ℝ) ^ d ≤ density) :
    400 * ((max r 1 : ℕ) : ℝ) *
        ((((mOne d rankCost : ℕ) : NNReal)⁻¹ : NNReal) : ℝ) ≤
      (1 / 512 : ℝ) * density / 4 := by
  change 400 * ((max r 1 : ℕ) : ℝ) *
      (mOne d rankCost : ℝ)⁻¹ ≤ (1 / 512 : ℝ) * density / 4
  have hmax := max_rank_le_rankCap hrankCost hrank
  have hboundNat :
      819200 * max r 1 * 2 ^ d ≤ mOne d rankCost := by
    unfold mOne
    exact Nat.mul_le_mul_right (2 ^ d)
      (Nat.mul_le_mul_left 819200 hmax)
  have hbound :
      (819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d ≤
        (mOne d rankCost : ℝ) := by
    exact_mod_cast hboundNat
  have hmPos : (0 : ℝ) < mOne d rankCost := by
    exact_mod_cast mOne_pos hrankCost
  have hbasePos :
      (0 : ℝ) < (819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d := by
    positivity
  have hinv :
      (mOne d rankCost : ℝ)⁻¹ ≤
        ((819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d)⁻¹ :=
    (inv_le_inv₀ hmPos hbasePos).2 hbound
  calc
    400 * ((max r 1 : ℕ) : ℝ) * (mOne d rankCost : ℝ)⁻¹ ≤
        400 * ((max r 1 : ℕ) : ℝ) *
          ((819200 : ℝ) * (max r 1 : ℕ) * (2 : ℝ) ^ d)⁻¹ := by
      gcongr
    _ = (1 / 2048 : ℝ) * (1 / (2 : ℝ) ^ d) := by
      have hrpos : (0 : ℝ) < (max r 1 : ℕ) := by positivity
      have hpowPos : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
      field_simp
      ring
    _ ≤ (1 / 2048 : ℝ) * density := by
      gcongr
    _ = (1 / 512 : ℝ) * density / 4 := by ring

/-- The second denominator is at least 200 times rank, enough for the
doubled-middle Holder-small inclusion. -/
lemma two_hundred_mul_max_rank_le_mTwo {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    200 * max r 1 ≤ mTwo d rankCost := by
  have hmax := max_rank_le_rankCap hrankCost hrank
  unfold mTwo
  calc
    200 * max r 1 ≤ 200 * rankCap d rankCost :=
      Nat.mul_le_mul_left 200 hmax
    _ ≤ 76800 * rankCap d rankCost * 2 ^ (d + 1) := by
      have hcoeff : 200 ≤ 76800 := by omega
      calc
        200 * rankCap d rankCost ≤ 76800 * rankCap d rankCost :=
          Nat.mul_le_mul_right _ hcoeff
        _ ≤ 76800 * rankCap d rankCost * 2 ^ (d + 1) :=
          Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)

/-- Concrete doubled-middle scale condition in the exact NNReal shape
needed by Holder approximation. -/
lemma two_inv_mTwo_le_rank_scale {d rankCost r : ℕ}
    (hrankCost : 0 < rankCost)
    (hrank : r ≤ rankCap d rankCost) :
    (mTwo d rankCost : NNReal)⁻¹ + (mTwo d rankCost : NNReal)⁻¹ ≤
      1 / (100 * (max r 1 : ℕ) : NNReal) := by
  have hden := two_hundred_mul_max_rank_le_mTwo hrankCost hrank
  have hleft : (0 : NNReal) < mTwo d rankCost := by
    exact_mod_cast mTwo_pos hrankCost
  have hright : (0 : NNReal) < 200 * (max r 1 : ℕ) := by
    positivity
  have hinv :
      (mTwo d rankCost : NNReal)⁻¹ ≤
        (200 * (max r 1 : ℕ) : NNReal)⁻¹ := by
    apply (inv_le_inv₀ hleft hright).2
    exact_mod_cast hden
  calc
    (mTwo d rankCost : NNReal)⁻¹ + (mTwo d rankCost : NNReal)⁻¹ ≤
        (200 * (max r 1 : ℕ) : NNReal)⁻¹ +
          (200 * (max r 1 : ℕ) : NNReal)⁻¹ :=
      add_le_add hinv hinv
    _ = 1 / (100 * (max r 1 : ℕ) : NNReal) := by
      have hrpos : (0 : NNReal) < (max r 1 : ℕ) := by positivity
      field_simp
      norm_num

end

end ConcreteNumerics

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/RawSupplyNumerics.lean` -/

section
/-!
# Scalar bookkeeping for the raw Kelley--Meka supply

This file contains numerical adapters for the q, sample-size, relative
Chang, and phase/tail bounds consumed by ConcreteSupply.
-/

open _root_.Finset
open scoped _root_.NNReal

namespace RawSupplyNumerics

noncomputable section

def approximationDelta : ℝ := 1 / 8192

def qQuant (alpha : ℝ) : ℕ := ⌈8192 / alpha⌉₊

def tailExponent (alpha : ℝ) : ℕ := Nat.clog 2 (qQuant alpha)

def sampleQBound (alpha : ℝ) : ℕ :=
  ⌈1 + Real.log (2 / alpha)⌉₊

def sampleKBound (alpha : ℝ) : ℕ :=
  Erdos140.crootSisaskSampleSize (sampleQBound alpha)
    ((approximationDelta / tailExponent alpha) / Real.exp 1)

def crootBeta (alpha : ℝ) (k : ℕ) : ℝ :=
  (alpha / 2) ^ k / 2

def changRankCost (alpha : ℝ) (k : ℕ) : ℕ :=
  ⌈8 * (1 + Real.log (2 / crootBeta alpha k))⌉₊

/-- Holder exponent used at dyadic scale d. -/
def holderExponent (d : ℕ) : ℕ := 4 * (d + 1)

/-- Even exponent at which the high balanced norm is tested. -/
def smoothingExponent (d : ℕ) : ℕ :=
  BalancedRestriction.stoppingExponent (1 / 8 : ℝ) (holderExponent d)

def dyadicAlphaExponent (d : ℕ) : ℕ :=
  2 + 2 * d * smoothingExponent d

/-- Conservative common lower bound for both sifted densities.  The
terminal proof gets this from the dyadic density bound and the high-norm
threshold; writing it as a reciprocal power of two makes positivity and
all later logarithms painless. -/
def dyadicSiftedAlpha (d : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ dyadicAlphaExponent d

/-- All rank increments from relative Chang are absorbed by this one
natural budget. -/
def dyadicRankCost (d : ℕ) : ℕ :=
  max 1 (changRankCost (dyadicSiftedAlpha d)
    (sampleKBound (dyadicSiftedAlpha d)))

def dyadicQQuant (d : ℕ) : ℕ := qQuant (dyadicSiftedAlpha d)

def dyadicTailExponent (d : ℕ) : ℕ :=
  tailExponent (dyadicSiftedAlpha d)

def dyadicSampleKBound (d : ℕ) : ℕ :=
  sampleKBound (dyadicSiftedAlpha d)

/-- A polynomial envelope for the Croot sample size. -/
def dyadicSamplePolynomial (d : ℕ) : ℕ :=
  2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3

def dyadicRankPolynomial (d : ℕ) : ℕ :=
  2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4

/-- The fixed coefficient after eliminating the intermediate dyadic
exponent from the rank-cost envelope. -/
def dyadicRankDegreeEightConstant : ℕ :=
  2 ^ 42 * 1720335 ^ 4

lemma approximationDelta_pos : 0 < approximationDelta := by
  norm_num [approximationDelta]

lemma holderExponent_pos (d : ℕ) : 0 < holderExponent d := by
  unfold holderExponent
  positivity

lemma smoothingExponent_pos (d : ℕ) : 0 < smoothingExponent d := by
  unfold smoothingExponent
  exact BalancedRestriction.stoppingExponent_pos (by norm_num) (holderExponent_pos d)

lemma smoothingExponent_even (d : ℕ) : Even (smoothingExponent d) := by
  unfold smoothingExponent
  exact BalancedRestriction.stoppingExponent_even _ _

lemma smoothingExponent_le (d : ℕ) :
    smoothingExponent d ≤ 860160 * (d + 1) := by
  have h :=
    BalancedRestriction.stoppingExponent_le_const_mul
      (ε := (1 / 8 : ℝ)) (p := holderExponent d) (holderExponent_pos d)
  norm_num [smoothingExponent, holderExponent, unbalancingMultiplier] at h ⊢
  omega

lemma dyadicAlphaExponent_le (d : ℕ) :
    dyadicAlphaExponent d ≤ 1720322 * (d + 1) ^ 2 := by
  unfold dyadicAlphaExponent
  have h := smoothingExponent_le d
  nlinarith [show d ≤ d + 1 by omega]

lemma dyadicSiftedAlpha_pos (d : ℕ) : 0 < dyadicSiftedAlpha d := by
  unfold dyadicSiftedAlpha
  positivity

lemma dyadicSiftedAlpha_le_one (d : ℕ) : dyadicSiftedAlpha d ≤ 1 := by
  unfold dyadicSiftedAlpha
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ dyadicAlphaExponent d := by
    exact one_le_pow₀ (by norm_num)
  exact (div_le_iff₀ (by positivity)).2
    (by simpa only [dyadicAlphaExponent, one_mul] using hpow)

lemma dyadicSiftedAlpha_le_two (d : ℕ) : dyadicSiftedAlpha d ≤ 2 :=
  (dyadicSiftedAlpha_le_one d).trans (by norm_num)

lemma dyadicRankCost_pos (d : ℕ) : 0 < dyadicRankCost d := by
  unfold dyadicRankCost
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

lemma dyadicQQuant_eq (d : ℕ) :
    dyadicQQuant d = 8192 * 2 ^ dyadicAlphaExponent d := by
  unfold dyadicQQuant qQuant dyadicSiftedAlpha
  have hpow : (0 : ℝ) < (2 : ℝ) ^ dyadicAlphaExponent d := by positivity
  rw [show (8192 : ℝ) / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
      ((8192 * 2 ^ dyadicAlphaExponent d : ℕ) : ℝ) by
        push_cast
        field_simp]
  exact Nat.ceil_natCast _

lemma dyadicTailExponent_eq (d : ℕ) :
    dyadicTailExponent d = 13 + dyadicAlphaExponent d := by
  unfold dyadicTailExponent tailExponent
  change Nat.clog 2 (dyadicQQuant d) = 13 + dyadicAlphaExponent d
  rw [dyadicQQuant_eq]
  rw [show (8192 : ℕ) = 2 ^ 13 by norm_num, ← pow_add,
    Nat.clog_pow 2 (13 + dyadicAlphaExponent d) (by norm_num)]

lemma sampleQBound_dyadic_le (d : ℕ) :
    sampleQBound (dyadicSiftedAlpha d) ≤ dyadicAlphaExponent d + 2 := by
  unfold sampleQBound dyadicSiftedAlpha
  apply Nat.ceil_le.mpr
  have hpow : (0 : ℝ) < (2 : ℝ) ^ dyadicAlphaExponent d := by positivity
  have harg :
      2 / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
        (2 : ℝ) ^ (dyadicAlphaExponent d + 1) := by
    field_simp
    rw [pow_succ]
    ring
  rw [harg, Real.log_pow]
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ dyadicAlphaExponent d + 1 by positivity)]

lemma dyadicSampleKBound_le_polynomial (d : ℕ) :
    dyadicSampleKBound d ≤ dyadicSamplePolynomial d := by
  unfold dyadicSampleKBound sampleKBound dyadicSamplePolynomial
  unfold Erdos140.crootSisaskSampleSize
  apply Nat.ceil_le.mpr
  have hq := sampleQBound_dyadic_le d
  have htail := dyadicTailExponent_eq d
  have hqR : (sampleQBound (dyadicSiftedAlpha d) : ℝ) ≤
      dyadicAlphaExponent d + 2 := by exact_mod_cast hq
  have htailR : (tailExponent (dyadicSiftedAlpha d) : ℝ) =
      dyadicAlphaExponent d + 13 := by
    change (dyadicTailExponent d : ℝ) =
      dyadicAlphaExponent d + 13
    exact_mod_cast (by simpa [Nat.add_comm] using htail)
  have hexp : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hE : (0 : ℝ) ≤ dyadicAlphaExponent d := by positivity
  rw [htailR]
  unfold approximationDelta
  have hden :
      (0 : ℝ) <
        (((1 / 8192 : ℝ) / (dyadicAlphaExponent d + 13)) /
          Real.exp 1 / 2) ^ 2 := by positivity
  apply (div_le_iff₀ hden).2
  have hE13 : (0 : ℝ) < dyadicAlphaExponent d + 13 := by positivity
  have hqE13 : (sampleQBound (dyadicSiftedAlpha d) : ℝ) ≤
      dyadicAlphaExponent d + 13 := by linarith
  have hexp2 : Real.exp 1 ^ 2 ≤ (9 : ℝ) := by
    nlinarith [Real.exp_pos (1 : ℝ)]
  field_simp
  push_cast
  calc
    64 * (sampleQBound (dyadicSiftedAlpha d) : ℝ) * 8192 ^ 2 *
        (dyadicAlphaExponent d + 13) ^ 2 * Real.exp 1 ^ 2 * 2 ^ 2 ≤
      64 * (dyadicAlphaExponent d + 13) * 8192 ^ 2 *
        (dyadicAlphaExponent d + 13) ^ 2 * 9 * 2 ^ 2 := by
          gcongr
    _ = (64 * 8192 ^ 2 * 9 * 2 ^ 2 : ℝ) *
        (dyadicAlphaExponent d + 13) ^ 3 := by ring
    _ ≤ (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 := by
      gcongr
      norm_num
    _ = (274877906944 : ℝ) *
        (dyadicAlphaExponent d + 13) ^ 3 := by norm_num

lemma qQuant_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < qQuant alpha := by
  unfold qQuant
  apply Nat.ceil_pos.2
  positivity

lemma qQuant_cast_lower {alpha : ℝ} (_halpha : 0 < alpha) :
    8192 / alpha ≤ (qQuant alpha : ℝ) := by
  exact Nat.le_ceil _

/-- If the final-to-middle cardinality ratio is at least alpha/2, the
localized Croot moment parameter is bounded by the canonical logarithmic
choice. -/
lemma sampleQ_le_sampleQBound {alpha ratio : ℝ}
    (halpha : 0 < alpha) (halpha_two : alpha ≤ 2)
    (hratio : alpha / 2 ≤ ratio) :
    ⌈1 + Real.log (min 1 ratio)⁻¹⌉₊ ≤ sampleQBound alpha := by
  have halphaHalf : 0 < alpha / 2 := by positivity
  have hhalfOne : alpha / 2 ≤ (1 : ℝ) := by linarith
  have hmin : alpha / 2 ≤ min 1 ratio := le_min hhalfOne hratio
  have hminPos : 0 < min 1 ratio := halphaHalf.trans_le hmin
  have hinv : (min 1 ratio)⁻¹ ≤ (alpha / 2)⁻¹ :=
    (inv_le_inv₀ hminPos halphaHalf).2 hmin
  have hlog : Real.log (min 1 ratio)⁻¹ ≤ Real.log (2 / alpha) := by
    have hrewrite : (alpha / 2)⁻¹ = 2 / alpha := by
      field_simp
    rw [← hrewrite]
    exact Real.log_le_log (by positivity) hinv
  unfold sampleQBound
  apply Nat.ceil_mono
  linarith

/-- Croot--Sisask's explicit sample count is monotone in its natural moment
parameter at every positive tolerance. -/
lemma crootSisaskSampleSize_mono_q {q Q : ℕ} {epsilon : ℝ}
    (hq : q ≤ Q) (hepsilon : 0 < epsilon) :
    Erdos140.crootSisaskSampleSize q epsilon ≤
      Erdos140.crootSisaskSampleSize Q epsilon := by
  unfold Erdos140.crootSisaskSampleSize
  apply Nat.ceil_mono
  have hden : 0 < (epsilon / 2) ^ 2 := by positivity
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.mul_le_mul_left 64 hq) hden.le

/-- Direct form used after the supported-popular cardinal bounds have supplied
the ratio alpha/2 ≤ |A₁|/|S|. -/
lemma localizedAPSampleK_le_sampleKBound
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (M L : Finset G) {alpha : ℝ}
    (halpha : 0 < alpha) (halpha_two : alpha ≤ 2)
    (hratio : alpha / 2 ≤ (L.card : ℝ) / M.card)
    (hm : 0 < tailExponent alpha) :
    DensityStep.localizedAPSampleK M L approximationDelta
        (tailExponent alpha) ≤ sampleKBound alpha := by
  unfold DensityStep.localizedAPSampleK sampleKBound
  apply crootSisaskSampleSize_mono_q
  · unfold DensityStep.localizedAPSampleQ
    exact sampleQ_le_sampleQBound halpha halpha_two hratio
  · have htail : (0 : ℝ) < tailExponent alpha := by exact_mod_cast hm
    exact div_pos (div_pos approximationDelta_pos htail) (Real.exp_pos _)

lemma tailExponent_pos {alpha : ℝ} (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1) :
    0 < tailExponent alpha := by
  unfold tailExponent
  have hq : 1 < qQuant alpha := by
    have hlarge : (1 : ℝ) < 8192 / alpha := by
      have : alpha < 8192 := by
        nlinarith
      exact (lt_div_iff₀ halpha).2 (by nlinarith)
    have hceil : 8192 / alpha ≤ (qQuant alpha : ℝ) := qQuant_cast_lower halpha
    exact_mod_cast hlarge.trans_le hceil
  exact Nat.clog_pos (by norm_num) hq

lemma two_pow_tailExponent_ge_qQuant {alpha : ℝ} (_halpha : 0 < alpha) :
    qQuant alpha ≤ 2 ^ tailExponent alpha := by
  unfold tailExponent
  exact Nat.le_pow_clog (by norm_num) _

lemma inv_two_pow_tailExponent_le {alpha : ℝ} (halpha : 0 < alpha) :
    (1 / 2 : ℝ) ^ tailExponent alpha ≤ alpha / 8192 := by
  have hq : (0 : ℝ) < qQuant alpha := by
    exact_mod_cast qQuant_pos halpha
  have hpow : (0 : ℝ) < (2 : ℝ) ^ tailExponent alpha := by positivity
  have hqpow : (qQuant alpha : ℝ) ≤ (2 : ℝ) ^ tailExponent alpha := by
    exact_mod_cast two_pow_tailExponent_ge_qQuant halpha
  have hceil : 8192 / alpha ≤ (qQuant alpha : ℝ) :=
    qQuant_cast_lower halpha
  calc
    (1 / 2 : ℝ) ^ tailExponent alpha =
        ((2 : ℝ) ^ tailExponent alpha)⁻¹ := by
          rw [one_div, inv_pow]
    _ ≤ (qQuant alpha : ℝ)⁻¹ :=
      (inv_le_inv₀ hpow hq).2 hqpow
    _ ≤ (8192 / alpha)⁻¹ := by
      have hbase : (0 : ℝ) < 8192 / alpha := by positivity
      exact (inv_le_inv₀ hq hbase).2 hceil
    _ = alpha / 8192 := by
      field_simp

lemma sqrt_two_div_le_two_div {alpha : ℝ}
    (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    Real.sqrt (2 / alpha) ≤ 2 / alpha := by
  have hone : (1 : ℝ) ≤ 2 / alpha := by
    apply (le_div_iff₀ halpha).2
    nlinarith
  have hnonneg : 0 ≤ 2 / alpha := by positivity
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · nlinarith

lemma quantized_phase_mul_sqrt_le
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    (2 / (qQuant alpha : ℝ)) * Real.sqrt (2 / alpha) ≤ 1 / 2048 := by
  have hq : (0 : ℝ) < qQuant alpha := by
    exact_mod_cast qQuant_pos halpha
  have hceil := qQuant_cast_lower halpha
  have hsqrt := sqrt_two_div_le_two_div halpha halpha_one
  calc
    (2 / (qQuant alpha : ℝ)) * Real.sqrt (2 / alpha) ≤
        (2 / (qQuant alpha : ℝ)) * (2 / alpha) := by
      gcongr
    _ ≤ (2 / (8192 / alpha)) * (2 / alpha) := by
      have hbase : (0 : ℝ) < 8192 / alpha := by positivity
      have hdiv : 2 / (qQuant alpha : ℝ) ≤ 2 / (8192 / alpha) := by
        exact div_le_div_of_nonneg_left (by norm_num) hbase hceil
      exact mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = 1 / 2048 := by
      field_simp
      norm_num

lemma dyadic_tail_mul_sqrt_le
    {alpha : ℝ} (halpha : 0 < alpha) (halpha_one : alpha ≤ 1) :
    (2 * (1 / 2 : ℝ) ^ tailExponent alpha) *
        Real.sqrt (2 / alpha) ≤ 1 / 2048 := by
  have htail := inv_two_pow_tailExponent_le halpha
  have hsqrt := sqrt_two_div_le_two_div halpha halpha_one
  calc
    (2 * (1 / 2 : ℝ) ^ tailExponent alpha) *
        Real.sqrt (2 / alpha) ≤
      (2 * (alpha / 8192)) * (2 / alpha) := by
        gcongr
    _ = 1 / 2048 := by
      field_simp
      norm_num

lemma crootBeta_pos {alpha : ℝ} {k : ℕ} (halpha : 0 < alpha) :
    0 < crootBeta alpha k := by
  unfold crootBeta
  positivity

lemma log_two_div_crootBeta_eq
    {alpha : ℝ} {k : ℕ} (halpha : 0 < alpha) :
    Real.log (2 / crootBeta alpha k) =
      Real.log 4 + (k : ℝ) * Real.log (2 / alpha) := by
  have hhalf : (0 : ℝ) < alpha / 2 := by positivity
  have harg :
      2 / crootBeta alpha k = 4 / (alpha / 2) ^ k := by
    unfold crootBeta
    field_simp
    ring
  rw [harg, Real.log_div (by norm_num) (pow_ne_zero _ hhalf.ne'),
    Real.log_pow, Real.log_div (by norm_num) halpha.ne',
    Real.log_div halpha.ne' (by norm_num)]
  push_cast
  ring

lemma dyadicRankCost_le_polynomial (d : ℕ) :
    dyadicRankCost d ≤ dyadicRankPolynomial d := by
  unfold dyadicRankCost dyadicRankPolynomial
  apply max_le
  · have hpos : 0 < 2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 := by
      positivity
    omega
  · unfold changRankCost
    apply Nat.ceil_le.mpr
    rw [log_two_div_crootBeta_eq (dyadicSiftedAlpha_pos d)]
    have hk := dyadicSampleKBound_le_polynomial d
    have hkR : (sampleKBound (dyadicSiftedAlpha d) : ℝ) ≤
        (2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3 : ℕ) := by
      exact_mod_cast hk
    have hlogtwo : Real.log (2 : ℝ) ≤ 1 := by
      convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
      norm_num
    have hlogfour : Real.log (4 : ℝ) ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have hmul := mul_le_mul_of_nonneg_left hlogtwo
        (show (0 : ℝ) ≤ 2 by norm_num)
      norm_num at hmul ⊢
      exact hmul
    have hlogalpha :
        Real.log (2 / dyadicSiftedAlpha d) ≤
          (dyadicAlphaExponent d + 1 : ℝ) := by
      unfold dyadicSiftedAlpha
      have harg :
          2 / (1 / (2 : ℝ) ^ dyadicAlphaExponent d) =
            (2 : ℝ) ^ (dyadicAlphaExponent d + 1) := by
        field_simp
        rw [pow_succ]
        ring
      rw [harg, Real.log_pow]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hlogtwo
        (show (0 : ℝ) ≤ (dyadicAlphaExponent d + 1 : ℕ) by positivity)]
    have hE1 :
        (dyadicAlphaExponent d + 1 : ℝ) ≤
          dyadicAlphaExponent d + 13 := by norm_num
    have hbig :
        (1 : ℝ) ≤ (dyadicAlphaExponent d + 13) ^ 4 := by
      have hEzero : (0 : ℝ) ≤ dyadicAlphaExponent d := by positivity
      have : (1 : ℝ) ≤ dyadicAlphaExponent d + 13 := by nlinarith
      exact one_le_pow₀ this
    have hlognonneg :
        0 ≤ Real.log (2 / dyadicSiftedAlpha d) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ (dyadicSiftedAlpha_pos d)).2
      nlinarith [dyadicSiftedAlpha_le_two d]
    have hkR' :
        (sampleKBound (dyadicSiftedAlpha d) : ℝ) ≤
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 := by
      norm_num at hkR ⊢
      exact hkR
    have hlogalpha' :
        Real.log (2 / dyadicSiftedAlpha d) ≤
          dyadicAlphaExponent d + 13 := hlogalpha.trans hE1
    have hmul :
        (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
            Real.log (2 / dyadicSiftedAlpha d) ≤
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 3 *
            (dyadicAlphaExponent d + 13) := by
      exact mul_le_mul hkR' hlogalpha' hlognonneg (by positivity)
    push_cast at ⊢
    calc
      8 * (1 + (Real.log 4 +
          (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
            Real.log (2 / dyadicSiftedAlpha d))) ≤
        8 * (1 + (2 +
          (2 ^ 38 * (dyadicAlphaExponent d + 13) ^ 3 : ℝ) *
            (dyadicAlphaExponent d + 13))) := by
              have hinner :
                  Real.log 4 +
                      (sampleKBound (dyadicSiftedAlpha d) : ℝ) *
                        Real.log (2 / dyadicSiftedAlpha d) ≤
                    2 + (2 ^ 38 : ℝ) *
                      (dyadicAlphaExponent d + 13) ^ 3 *
                        (dyadicAlphaExponent d + 13) := by
                linarith
              nlinarith
      _ = 8 * (3 +
          (2 ^ 38 : ℝ) * (dyadicAlphaExponent d + 13) ^ 4) := by ring
      _ ≤ (2 ^ 42 : ℝ) * (dyadicAlphaExponent d + 13) ^ 4 := by
        norm_num at ⊢
        nlinarith
      _ = (4398046511104 : ℝ) *
          (dyadicAlphaExponent d + 13) ^ 4 := by norm_num

/-- The local-Chang rank cost is polynomial of degree eight in the dyadic
density index.  This is the form used by the final source-volume budget. -/
lemma dyadicRankCost_le_degree_eight (d : ℕ) :
    dyadicRankCost d ≤
      dyadicRankDegreeEightConstant * (d + 1) ^ 8 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hE13 :
      dyadicAlphaExponent d + 13 ≤ 1720335 * (d + 1) ^ 2 := by
    nlinarith
  calc
    dyadicRankCost d ≤
        2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 :=
      dyadicRankCost_le_polynomial d
    _ ≤ 2 ^ 42 * (1720335 * (d + 1) ^ 2) ^ 4 := by
      gcongr
    _ = dyadicRankDegreeEightConstant * (d + 1) ^ 8 := by
      unfold dyadicRankDegreeEightConstant
      ring

/-- The accumulated rank cap has degree nine after inserting the fixed
degree-eight local-Chang budget. -/
lemma dyadicRankCap_le_degree_nine (d : ℕ) :
    ConcreteNumerics.rankCap d (dyadicRankCost d) ≤
      (1024 * dyadicRankDegreeEightConstant) * (d + 1) ^ 9 := by
  unfold ConcreteNumerics.rankCap
  calc
    1024 * (d + 1) * dyadicRankCost d ≤
        1024 * (d + 1) *
          (dyadicRankDegreeEightConstant * (d + 1) ^ 8) := by
      gcongr
      exact dyadicRankCost_le_degree_eight d
    _ = (1024 * dyadicRankDegreeEightConstant) * (d + 1) ^ 9 := by
      ring

/-- A tiny reusable numerical estimate that keeps logarithmic losses
polynomial instead of replacing them by their (much larger) arguments. -/
lemma log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h :=
    Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

lemma log_natCast_le_natCast {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ n := by
  have h := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < n by exact_mod_cast hn)
  nlinarith

/-- The quantization logarithm is exactly linear in the dyadic exponent. -/
lemma log_dyadicQQuant_le_exponent (d : ℕ) :
    Real.log (dyadicQQuant d : ℝ) ≤
      (dyadicAlphaExponent d + 13 : ℝ) := by
  rw [dyadicQQuant_eq]
  push_cast
  rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, ← pow_add,
    Real.log_pow]
  push_cast
  have hnonneg : (0 : ℝ) ≤ 13 + dyadicAlphaExponent d := by positivity
  nlinarith [mul_le_mul_of_nonneg_left log_two_le_one hnonneg]

/-- Degree-two version of the preceding quantization-log bound. -/
lemma log_dyadicQQuant_le_degree_two (d : ℕ) :
    Real.log (dyadicQQuant d : ℝ) ≤
      1720335 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hE13 :
      dyadicAlphaExponent d + 13 ≤ 1720335 * (d + 1) ^ 2 := by
    nlinarith
  calc
    Real.log (dyadicQQuant d : ℝ) ≤
        (dyadicAlphaExponent d + 13 : ℝ) :=
      log_dyadicQQuant_le_exponent d
    _ ≤ 1720335 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hE13

/-- The logarithm of the rank cost stays linear in the dyadic exponent,
even though the rank cost itself has degree four in that exponent. -/
lemma log_dyadicRankCost_le_exponent (d : ℕ) :
    Real.log (dyadicRankCost d : ℝ) ≤
      42 + 4 * (dyadicAlphaExponent d + 13 : ℝ) := by
  have hcost := dyadicRankCost_le_polynomial d
  have hcostR :
      (dyadicRankCost d : ℝ) ≤
        ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) := by
    exact_mod_cast hcost
  have hcostPosR : (0 : ℝ) < dyadicRankCost d := by
    exact_mod_cast dyadicRankCost_pos d
  have hlog :
      Real.log (dyadicRankCost d : ℝ) ≤
        Real.log ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) :=
    Real.log_le_log hcostPosR hcostR
  have hpolylog :
      Real.log ((2 ^ 42 * (dyadicAlphaExponent d + 13) ^ 4 : ℕ) : ℝ) =
        42 * Real.log 2 +
          4 * Real.log ((dyadicAlphaExponent d + 13 : ℕ) : ℝ) := by
    push_cast
    rw [show (4398046511104 : ℝ) = (2 : ℝ) ^ 42 by norm_num]
    rw [Real.log_mul (pow_ne_zero _ (by norm_num))
      (pow_ne_zero _ (by positivity)),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hE13pos : 0 < dyadicAlphaExponent d + 13 := by positivity
  have hlogE13 :
      Real.log ((dyadicAlphaExponent d + 13 : ℕ) : ℝ) ≤
        (dyadicAlphaExponent d + 13 : ℕ) :=
    log_natCast_le_natCast hE13pos
  rw [hpolylog] at hlog
  have hfortytwo : 42 * Real.log (2 : ℝ) ≤ 42 := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 42 by norm_num)]
  have hfourE13 := mul_le_mul_of_nonneg_left hlogE13
    (show (0 : ℝ) ≤ 4 by norm_num)
  push_cast at hlog hfourE13
  nlinarith

/-- Degree-two form of the rank-cost logarithm. -/
lemma log_dyadicRankCost_le_degree_two (d : ℕ) :
    Real.log (dyadicRankCost d : ℝ) ≤
      6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hE := dyadicAlphaExponent_le d
  have hsq : 1 ≤ (d + 1) ^ 2 := by
    exact one_le_pow₀ (by omega)
  have hEbound :
      42 + 4 * (dyadicAlphaExponent d + 13) ≤
        6881382 * (d + 1) ^ 2 := by
    nlinarith
  calc
    Real.log (dyadicRankCost d : ℝ) ≤
        42 + 4 * (dyadicAlphaExponent d + 13 : ℝ) :=
      log_dyadicRankCost_le_exponent d
    _ ≤ 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hEbound

/-- The spectral factor `8R+1` has only a logarithmic cost in a positive
rank budget R. -/
lemma log_eight_mul_add_one_le_log
    {R : ℕ} (hR : 0 < R) :
    Real.log ((8 * R + 1 : ℕ) : ℝ) ≤
      9 + Real.log (R : ℝ) := by
  have hRone : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR.ne'
  have hnat : 8 * R + 1 ≤ 9 * R := by omega
  have hargPos : (0 : ℝ) < ((8 * R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 8 * R + 1 by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog :
      Real.log ((8 * R + 1 : ℕ) : ℝ) ≤
        Real.log ((9 * R : ℕ) : ℝ) :=
    Real.log_le_log hargPos (by exact_mod_cast hnat)
  have hprod :
      Real.log ((9 * R : ℕ) : ℝ) =
        Real.log 9 + Real.log (R : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hRpos.ne']
  rw [hprod] at hlog
  have h9 : Real.log (9 : ℝ) ≤ 9 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Logarithmic cost of the uniform quantization times spectral-cell base
used by the dyadic cell multiplier. -/
lemma log_dyadicSampleBase_le_degree_two (d : ℕ) :
    Real.log
        ((dyadicQQuant d * (8 * dyadicRankCost d + 1 : ℕ) : ℕ) : ℝ) ≤
      8601726 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hqPos : 0 < dyadicQQuant d := by
    unfold dyadicQQuant
    exact qQuant_pos (dyadicSiftedAlpha_pos d)
  have hRpos := dyadicRankCost_pos d
  have hqPosR : (0 : ℝ) < dyadicQQuant d := by exact_mod_cast hqPos
  have hcellPosR : (0 : ℝ) < 8 * dyadicRankCost d + 1 := by positivity
  have hlogQ := log_dyadicQQuant_le_degree_two d
  have hlogCell := log_eight_mul_add_one_le_log hRpos
  have hlogR := log_dyadicRankCost_le_degree_two d
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  push_cast
  rw [Real.log_mul hqPosR.ne' hcellPosR.ne']
  push_cast at hlogQ hlogR hsqOne hlogCell
  nlinarith

/-- The accumulated rank cap has only a degree-two logarithmic loss when
the dyadic local-Chang rank cost is substituted. -/
lemma log_dyadicRankCap_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hcostPos := dyadicRankCost_pos d
  have hcostPosR : (0 : ℝ) < dyadicRankCost d := by
    exact_mod_cast hcostPos
  have hdPos : 0 < d + 1 := by omega
  have hdPosR : (0 : ℝ) < d + 1 := by exact_mod_cast hdPos
  have hlogd : Real.log ((d + 1 : ℕ) : ℝ) ≤ (d + 1 : ℕ) :=
    log_natCast_le_natCast hdPos
  have hlogcost := log_dyadicRankCost_le_degree_two d
  have hsqR : ((d + 1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  unfold ConcreteNumerics.rankCap
  push_cast
  rw [Real.log_mul
      (mul_ne_zero (by norm_num) hdPosR.ne') hcostPosR.ne',
    Real.log_mul (by norm_num) hdPosR.ne']
  have hlog1024 : Real.log (1024 : ℝ) ≤ 10 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 10 by norm_num)]
  push_cast at hlogd hlogcost hsqR ⊢
  have hsqOne : (1 : ℝ) ≤ (↑d + 1) ^ 2 := by
    nlinarith
  nlinarith

lemma log_dyadicMOne_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.mOne d (dyadicRankCost d) : ℝ) ≤
      7700594 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hR := log_dyadicRankCap_le_degree_two d
  have hconst : Real.log (819200 : ℝ) ≤ 819200 :=
    log_natCast_le_natCast (by norm_num)
  have hpow : (d : ℝ) * Real.log 2 ≤ d := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ d by positivity)]
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hdSq : (d : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hd : (d : ℝ) ≤ d + 1 := by norm_num
    push_cast at hsqOne ⊢
    nlinarith
  have hRpos : 0 < ConcreteNumerics.rankCap d (dyadicRankCost d) :=
    ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hRposR : (0 : ℝ) <
      ConcreteNumerics.rankCap d (dyadicRankCost d) := by
    exact_mod_cast hRpos
  unfold ConcreteNumerics.mOne
  push_cast
  rw [Real.log_mul (mul_ne_zero (by norm_num) hRposR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hRposR.ne', Real.log_pow]
  push_cast at hR hpow hdSq ⊢
  nlinarith

lemma log_dyadicMTwo_le_degree_two (d : ℕ) :
    Real.log
        (ConcreteNumerics.mTwo d (dyadicRankCost d) : ℝ) ≤
      6958194 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  have hR := log_dyadicRankCap_le_degree_two d
  have hconst : Real.log (76800 : ℝ) ≤ 76800 :=
    log_natCast_le_natCast (by norm_num)
  have hpow : ((d + 1 : ℕ) : ℝ) * Real.log 2 ≤ d + 1 := by
    have hmul := mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) by positivity)
    norm_num at hmul ⊢
    exact hmul
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hdSq : ((d + 1 : ℕ) : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hRpos : 0 < ConcreteNumerics.rankCap d (dyadicRankCost d) :=
    ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hRposR : (0 : ℝ) <
      ConcreteNumerics.rankCap d (dyadicRankCost d) := by
    exact_mod_cast hRpos
  unfold ConcreteNumerics.mTwo
  push_cast
  rw [Real.log_mul (mul_ne_zero (by norm_num) hRposR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hRposR.ne', Real.log_pow]
  push_cast at hR hpow hdSq ⊢
  nlinarith

/-- Logarithmic envelope for the exact natural expression used by
`ConcreteSupply.dyadicHierarchyDenominator`.  Keeping the statement at the
formula level avoids an import cycle while allowing `simpa` at the call site.
-/
lemma log_dyadicHierarchyFormula_le_of_rankCap
    (d rankCap : ℕ) (hrankCap : 0 < rankCap) {LR : ℝ}
    (hlogRankCap : Real.log (rankCap : ℝ) ≤ LR) :
    Real.log
        ((8388608 * max rankCap 1 *
          2 ^ dyadicAlphaExponent d : ℕ) : ℝ) ≤
      23 + LR + dyadicAlphaExponent d := by
  have hmax : max rankCap 1 = rankCap :=
    max_eq_left (Nat.one_le_iff_ne_zero.mpr hrankCap.ne')
  rw [hmax]
  have hrankCapR : (0 : ℝ) < rankCap := by exact_mod_cast hrankCap
  have hlogConst : Real.log (8388608 : ℝ) ≤ 23 := by
    rw [show (8388608 : ℝ) = 2 ^ 23 by norm_num, Real.log_pow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 23 by norm_num)]
  have hlogPow :
      (dyadicAlphaExponent d : ℝ) * Real.log 2 ≤
        dyadicAlphaExponent d := by
    nlinarith [mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ dyadicAlphaExponent d by positivity)]
  push_cast
  rw [Real.log_mul
      (mul_ne_zero (by norm_num) hrankCapR.ne')
      (pow_ne_zero _ (by norm_num)),
    Real.log_mul (by norm_num) hrankCapR.ne', Real.log_pow]
  nlinarith

lemma dyadic_quantized_phase_mul_sqrt_le (d : ℕ) :
    (2 / (dyadicQQuant d : ℝ)) *
        Real.sqrt (2 / dyadicSiftedAlpha d) ≤ 1 / 2048 := by
  unfold dyadicQQuant
  exact quantized_phase_mul_sqrt_le
    (dyadicSiftedAlpha_pos d) (dyadicSiftedAlpha_le_one d)

lemma dyadic_tail_error_mul_sqrt_le (d : ℕ) :
    (2 * (1 / 2 : ℝ) ^ dyadicTailExponent d) *
        Real.sqrt (2 / dyadicSiftedAlpha d) ≤ 1 / 2048 := by
  unfold dyadicTailExponent
  exact dyadic_tail_mul_sqrt_le
    (dyadicSiftedAlpha_pos d) (dyadicSiftedAlpha_le_one d)

/-! ## Source and multiplier losses -/

/-- The exact natural multiplier occurring in the commuted relative-T
localized package. -/
def cellMultiplier (rank delta n : ℕ) : ℕ :=
  n ^ delta * 4 ^ (rank + delta)

/-- Fixed multiplier envelope after replacing the actual dimension and
spectral cell count by their dyadic bounds. -/
def dyadicCellMultiplier (d : ℕ) : ℕ :=
  cellMultiplier
    (ConcreteNumerics.rankCap d (dyadicRankCost d))
    (dyadicRankCost d)
    (dyadicQQuant d * (8 * dyadicRankCost d + 1))

/-- Coefficient in the degree-ten logarithmic envelope for the preceding
cell multiplier. -/
def dyadicCellLogConstant : ℕ :=
  dyadicRankDegreeEightConstant * 8601726 +
    2 * (1024 * dyadicRankDegreeEightConstant +
      dyadicRankDegreeEightConstant)

/-- Formula-level versions of the finite losses defined in
`ConcreteSupply`; these avoid an import cycle and are discharged there by
`simpa` after unfolding the concrete definitions. -/
def reciprocalLossFormula (rank m : ℕ) : ℕ :=
  (3 * m) ^ rank * 4 ^ rank

def twoReciprocalLossFormula (rank mOne mTwo : ℕ) : ℕ :=
  reciprocalLossFormula rank mOne * reciprocalLossFormula rank mTwo

def smoothingHierarchyLossFormula (rank : ℕ) : ℕ :=
  reciprocalLossFormula rank (1600 * max rank 1) *
    reciprocalLossFormula rank (200 * max rank 1) *
      reciprocalLossFormula rank (200 * max rank 1)

def dyadicHierarchyFormula (d rankCap : ℕ) : ℕ :=
  8388608 * max rankCap 1 * 2 ^ dyadicAlphaExponent d

/-- Coarse monotonicity of the exact cell multiplier. -/
lemma cellMultiplier_mono
    {rank delta n R D N : ℕ}
    (hn : 0 < n) (hnN : n ≤ N)
    (hrank : rank ≤ R) (hdelta : delta ≤ D) :
    cellMultiplier rank delta n ≤ cellMultiplier R D N := by
  unfold cellMultiplier
  have hN : 0 < N := hn.trans_le hnN
  have hfirst : n ^ delta ≤ N ^ D := by
    calc
      n ^ delta ≤ N ^ delta := Nat.pow_le_pow_left hnN _
      _ ≤ N ^ D := Nat.pow_le_pow_right hN hdelta
  have hsecond : 4 ^ (rank + delta) ≤ 4 ^ (R + D) := by
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.add_le_add hrank hdelta
  exact Nat.mul_le_mul hfirst hsecond

lemma ceil_eight_mul_rank_add_one_eq (R : ℕ) :
    ⌈8 * (R : ℝ)⌉₊ + 1 = 8 * R + 1 := by
  rw [show 8 * (R : ℝ) = ((8 * R : ℕ) : ℝ) by
    push_cast
    ring]
  rw [Nat.ceil_natCast]

/-- Reciprocal denominator for the local-Chang regular scale followed by a
further reciprocal source scale.  The factor 200 pays for rho ≥ 1/2. -/
def sourceDenominator (rank cap m : ℕ) : ℕ :=
  200 * max rank 1 * (2 * cap + 1) * m

lemma sourceDenominator_pos {rank cap m : ℕ} (hm : 0 < m) :
    0 < sourceDenominator rank cap m := by
  unfold sourceDenominator
  positivity

/-- Exact additive logarithm of the nested local-Chang/source reciprocal
denominator. -/
lemma log_sourceDenominator {rank cap m : ℕ} (hm : 0 < m) :
    Real.log (sourceDenominator rank cap m : ℝ) =
      Real.log 200 + Real.log ((max rank 1 : ℕ) : ℝ) +
        Real.log ((2 * cap + 1 : ℕ) : ℝ) + Real.log (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold sourceDenominator
  push_cast
  rw [Real.log_mul (by positivity) hmR.ne',
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity)]

/-- Monotone logarithmic envelope for the source denominator.  The constant
200 is intentionally left coarse; it is harmless in the final polynomial. -/
lemma log_sourceDenominator_le_of_bounds
    {rank cap m : ℕ} {LR LC LM : ℝ} (hm : 0 < m)
    (hRank : Real.log ((max rank 1 : ℕ) : ℝ) ≤ LR)
    (hCap : Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤ LC)
    (hM : Real.log (m : ℝ) ≤ LM) :
    Real.log (sourceDenominator rank cap m : ℝ) ≤
      200 + LR + LC + LM := by
  rw [log_sourceDenominator hm]
  have h200 : Real.log (200 : ℝ) ≤ 200 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Replacing a current rank by a positive uniform rank cap costs no extra
logarithmic factor. -/
lemma log_max_rank_le_log_rankCap
    {rank rankCap : ℕ} (hrankCap : 0 < rankCap) (hrank : rank ≤ rankCap) :
    Real.log ((max rank 1 : ℕ) : ℝ) ≤ Real.log (rankCap : ℝ) := by
  have hmax : max rank 1 ≤ rankCap :=
    max_le hrank (Nat.one_le_iff_ne_zero.mpr hrankCap.ne')
  have hmaxPos : (0 : ℝ) < max rank 1 := by positivity
  exact Real.log_le_log hmaxPos (by exact_mod_cast hmax)

/-- When the local-Chang cap is at most eight times a positive rank budget,
its logarithm is still just the logarithm of that budget plus a constant. -/
lemma log_two_mul_add_one_le_of_cap_le_eight_mul
    {cap R : ℕ} (hR : 0 < R) (hcap : cap ≤ 8 * R) :
    Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
      17 + Real.log (R : ℝ) := by
  have hRone : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR.ne'
  have hnat : 2 * cap + 1 ≤ 17 * R := by
    nlinarith
  have hargPos : (0 : ℝ) < ((2 * cap + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * cap + 1 by positivity)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hlog :
      Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
        Real.log ((17 * R : ℕ) : ℝ) :=
    Real.log_le_log hargPos (by exact_mod_cast hnat)
  have hprod :
      Real.log ((17 * R : ℕ) : ℝ) =
        Real.log 17 + Real.log (R : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hRpos.ne']
  rw [hprod] at hlog
  have h17 : Real.log (17 : ℝ) ≤ 17 :=
    log_natCast_le_natCast (by norm_num)
  nlinarith

/-- Fully concrete degree-two logarithmic budget for the nested source
denominator.  The rank and local-Chang cap hypotheses are exactly the two
facts exposed by the dyadic hierarchy adapter. -/
lemma log_sourceDenominator_dyadicFormula_le_degree_two
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log
        (sourceDenominator rank cap
          (8388608 *
            max (ConcreteNumerics.rankCap d (dyadicRankCost d)) 1 *
              2 ^ dyadicAlphaExponent d) : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let m := 8388608 * max R 1 * 2 ^ dyadicAlphaExponent d
  have hRpos : 0 < R := by
    unfold R
    exact ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hm : 0 < m := by
    unfold m
    positivity
  have hlogR : Real.log (R : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [R] using log_dyadicRankCap_le_degree_two d
  have hlogRank : Real.log ((max rank 1 : ℕ) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 :=
    (log_max_rank_le_log_rankCap hRpos (by simpa [R] using hrank)).trans hlogR
  have hlogCap : Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
      17 + 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      Real.log ((2 * cap + 1 : ℕ) : ℝ) ≤
          17 + Real.log (dyadicRankCost d : ℝ) :=
        log_two_mul_add_one_le_of_cap_le_eight_mul
          (dyadicRankCost_pos d) hcap
      _ ≤ 17 + 6881382 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
        gcongr
        exact log_dyadicRankCost_le_degree_two d
  have hlogM : Real.log (m : ℝ) ≤
      23 + 8601715 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hraw := log_dyadicHierarchyFormula_le_of_rankCap d R hRpos hlogR
    have hE := dyadicAlphaExponent_le d
    have hER : (dyadicAlphaExponent d : ℝ) ≤
        1720322 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hE
    unfold m
    nlinarith
  have hsource := log_sourceDenominator_le_of_bounds
    (rank := rank) (cap := cap) (m := m) hm hlogRank hlogCap hlogM
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  simpa [m, R] using (by nlinarith :
    Real.log (sourceDenominator rank cap m : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2)

/-- The source-volume power contributes degree eleven after multiplying its
degree-two logarithm by the degree-nine ambient rank cap. -/
lemma log_sourcePow_dyadicFormula_le_degree_eleven
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log
        (((3 * sourceDenominator rank cap
          (dyadicHierarchyFormula d
            (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank : ℕ) : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 22364733 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let m := dyadicHierarchyFormula d R
  let P := sourceDenominator rank cap m
  have hm : 0 < m := by
    unfold m dyadicHierarchyFormula
    positivity
  have hP : 0 < P := by
    unfold P
    exact sourceDenominator_pos hm
  have hlogP : Real.log (P : ℝ) ≤
      22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [P, m, R, dyadicHierarchyFormula] using
      log_sourceDenominator_dyadicFormula_le_degree_two d rank cap hrank hcap
  have hlog3P : Real.log ((3 * P : ℕ) : ℝ) ≤
      3 + 22364730 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hPR : (0 : ℝ) < P := by exact_mod_cast hP
    have h3 : Real.log (3 : ℝ) ≤ 3 :=
      log_natCast_le_natCast (by norm_num)
    rw [show ((3 * P : ℕ) : ℝ) = (3 : ℝ) * (P : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hPR.ne']
    nlinarith
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hfactor : Real.log ((3 * P : ℕ) : ℝ) ≤
      22364733 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by simpa [R] using hrank)
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        simpa [R] using (show
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
            (1024 * dyadicRankDegreeEightConstant : ℕ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 by
          exact_mod_cast dyadicRankCap_le_degree_nine d)
  have hfactorNonneg : 0 ≤ Real.log ((3 * P : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 3 * P by omega)
  have hmul := mul_le_mul hrankR hfactor hfactorNonneg (by positivity)
  push_cast
  rw [Real.log_pow]
  push_cast at hmul ⊢
  nlinarith

/-- The explicit source denominator is below the actual nested
local-Chang/source scale whenever the final source scale is 1/m. -/
lemma inv_sourceDenominator_le_localChang_source_scale
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (T : Finset G) (eta : ℝ) (m : ℕ)
    (hm : 0 < m) (rho : NNReal) (hrho : 1 / 2 ≤ rho) :
    ((sourceDenominator B.rank
        (RelativeChangSanders.localChangCap B T eta) m : NNReal)⁻¹) ≤
      rho * RelativeChangSanders.localChangBaseScale B T eta *
        (m : NNReal)⁻¹ := by
  unfold sourceDenominator RelativeChangSanders.localChangBaseScale
  have hrank : (0 : NNReal) < max B.rank 1 := by positivity
  have hcap : (0 : NNReal) <
      (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) := by
    positivity
  have hm' : (0 : NNReal) < m := by exact_mod_cast hm
  have hmul :
      (200 * (max B.rank 1 : NNReal) *
          (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) *
          (m : NNReal)) * (1 / 2) ≤
        (200 * (max B.rank 1 : NNReal) *
          (2 * RelativeChangSanders.localChangCap B T eta + 1 : ℕ) *
          (m : NNReal)) * rho := by
    exact mul_le_mul_of_nonneg_left hrho (by positivity)
  field_simp
  norm_num at hmul ⊢
  convert hmul using 1 <;> ring

/-- One reciprocal natural scale controls an arbitrary target scale above
it, with the clean three-P-to-rank loss from BohrScaleVolume. -/
lemma card_unit_le_three_mul_pow_rank_mul_card_dilate_of_inv_nat_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (B : BohrData G) (P : ℕ) (hP : 0 < P) {rho : NNReal}
    (hrho : ((P : NNReal)⁻¹) ≤ rho) :
    B.carrier.card ≤
      (3 * P) ^ B.rank * (B.dilate rho).carrier.card := by
  have hbase :=
    BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div B 1 hP
  have hmono :
      (B.dilate ((P : NNReal)⁻¹)).carrier.card ≤
        (B.dilate rho).carrier.card :=
    Finset.card_le_card (BohrData.carrier_dilate_mono hrho)
  calc
    B.carrier.card = (B.dilate 1).carrier.card := by simp
    _ ≤ (3 * P) ^ B.rank *
        (B.dilate ((P : NNReal)⁻¹)).carrier.card := by
          simpa [div_eq_mul_inv] using hbase
    _ ≤ (3 * P) ^ B.rank * (B.dilate rho).carrier.card :=
      Nat.mul_le_mul_left _ hmono

/-- Real logarithm of the exact cell multiplier. -/
lemma log_cellMultiplier
    {rank delta n : ℕ} (hn : 0 < n) :
    Real.log (cellMultiplier rank delta n : ℝ) =
      (delta : ℝ) * Real.log (n : ℝ) +
        (rank + delta : ℝ) * Real.log 4 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold cellMultiplier
  push_cast
  rw [Real.log_mul (pow_ne_zero _ hnR.ne') (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma reciprocalLossFormula_pos {rank m : ℕ} (hm : 0 < m) :
    0 < reciprocalLossFormula rank m := by
  unfold reciprocalLossFormula
  positivity

lemma log_reciprocalLossFormula {rank m : ℕ} (hm : 0 < m) :
    Real.log (reciprocalLossFormula rank m : ℝ) =
      (rank : ℝ) *
        (Real.log ((3 * m : ℕ) : ℝ) + Real.log 4) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold reciprocalLossFormula
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (mul_ne_zero (by norm_num) hmR.ne'))
      (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]
  push_cast
  ring

lemma log_twoReciprocalLossFormula {rank mOne mTwo : ℕ}
    (hmOne : 0 < mOne) (hmTwo : 0 < mTwo) :
    Real.log (twoReciprocalLossFormula rank mOne mTwo : ℝ) =
      (rank : ℝ) *
        (Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4) +
      (rank : ℝ) *
        (Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4) := by
  unfold twoReciprocalLossFormula
  push_cast
  rw [Real.log_mul
      (by exact_mod_cast (reciprocalLossFormula_pos hmOne).ne')
      (by exact_mod_cast (reciprocalLossFormula_pos hmTwo).ne'),
    log_reciprocalLossFormula hmOne, log_reciprocalLossFormula hmTwo]
  push_cast
  ring

lemma log_smoothingHierarchyLossFormula (rank : ℕ) :
    Real.log (smoothingHierarchyLossFormula rank : ℝ) =
      (rank : ℝ) *
          (Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) +
        (rank : ℝ) *
          (Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) +
        (rank : ℝ) *
          (Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) +
            Real.log 4) := by
  have hmax : 0 < max rank 1 := by positivity
  have h1600 : 0 < 1600 * max rank 1 := by positivity
  have h200 : 0 < 200 * max rank 1 := by positivity
  have hAne :
      ((reciprocalLossFormula rank (1600 * max rank 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (reciprocalLossFormula_pos h1600).ne'
  have hBne :
      ((reciprocalLossFormula rank (200 * max rank 1) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (reciprocalLossFormula_pos h200).ne'
  unfold smoothingHierarchyLossFormula
  push_cast
  rw [Real.log_mul
      (mul_ne_zero hAne hBne) hBne,
    Real.log_mul hAne hBne,
    log_reciprocalLossFormula h1600,
    log_reciprocalLossFormula h200]
  push_cast
  ring

lemma log_three_mul_le_of_log_le
    {m : ℕ} {L : ℝ} (hm : 0 < m)
    (hlog : Real.log (m : ℝ) ≤ L) :
    Real.log ((3 * m : ℕ) : ℝ) ≤ 3 + L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : Real.log (3 : ℝ) ≤ 3 :=
    log_natCast_le_natCast (by norm_num)
  push_cast
  rw [Real.log_mul (by norm_num) hmR.ne']
  nlinarith

lemma log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_left log_two_le_one
    (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at hmul ⊢
  exact hmul

/-- Logarithmic loss of the two reciprocal regular children at the concrete
first and second scales. -/
lemma log_twoReciprocalLossFormula_dyadic_le_degree_eleven
    (d rank : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d)) :
    Real.log
        (twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne d (dyadicRankCost d))
          (ConcreteNumerics.mTwo d (dyadicRankCost d)) : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 14658798 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let mOne := ConcreteNumerics.mOne d (dyadicRankCost d)
  let mTwo := ConcreteNumerics.mTwo d (dyadicRankCost d)
  have hmOne : 0 < mOne := by
    unfold mOne
    exact ConcreteNumerics.mOne_pos (dyadicRankCost_pos d)
  have hmTwo : 0 < mTwo := by
    unfold mTwo
    exact ConcreteNumerics.mTwo_pos (dyadicRankCost_pos d)
  have hlogMOne : Real.log (mOne : ℝ) ≤
      7700594 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [mOne] using log_dyadicMOne_le_degree_two d
  have hlogMTwo : Real.log (mTwo : ℝ) ≤
      6958194 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [mTwo] using log_dyadicMTwo_le_degree_two d
  have hlog3One := log_three_mul_le_of_log_le hmOne hlogMOne
  have hlog3Two := log_three_mul_le_of_log_le hmTwo hlogMTwo
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hfactorOne :
      Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4 ≤
        7700599 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hfactorTwo :
      Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4 ≤
        6958199 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) := by
        exact_mod_cast hrank
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        exact_mod_cast dyadicRankCap_le_degree_nine d
  have hfactorOneNonneg :
      0 ≤ Real.log ((3 * mOne : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * mOne : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * mOne by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hfactorTwoNonneg :
      0 ≤ Real.log ((3 * mTwo : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * mTwo : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * mTwo by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  rw [log_twoReciprocalLossFormula hmOne hmTwo]
  have htermOne := mul_le_mul hrankR hfactorOne hfactorOneNonneg (by positivity)
  have htermTwo := mul_le_mul hrankR hfactorTwo hfactorTwoNonneg (by positivity)
  push_cast at htermOne htermTwo ⊢
  nlinarith

/-- Logarithmic loss of the three fixed smoothing-hierarchy children. -/
lemma log_smoothingHierarchyLossFormula_dyadic_le_degree_eleven
    (d rank : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d)) :
    Real.log (smoothingHierarchyLossFormula rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 20646194 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  have hRpos : 0 < R := by
    unfold R
    exact ConcreteNumerics.rankCap_pos (dyadicRankCost_pos d)
  have hlogR : Real.log (R : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [R] using log_dyadicRankCap_le_degree_two d
  have hlogMax : Real.log ((max rank 1 : ℕ) : ℝ) ≤
      6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 :=
    (log_max_rank_le_log_rankCap hRpos (by simpa [R] using hrank)).trans hlogR
  have hmaxPos : 0 < max rank 1 := by positivity
  have hmaxPosR : (0 : ℝ) < max rank 1 := by exact_mod_cast hmaxPos
  have hsqOne : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) ^ 2 := by
    have hdone : (1 : ℝ) ≤ (d + 1 : ℕ) := by
      exact_mod_cast (show 1 ≤ d + 1 by omega)
    nlinarith
  have hlogEta :
      Real.log ((1600 * max rank 1 : ℕ) : ℝ) ≤
        1600 + 6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show ((1600 * max rank 1 : ℕ) : ℝ) =
        (1600 : ℝ) * ((max rank 1 : ℕ) : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hmaxPosR.ne']
    have h1600 : Real.log (1600 : ℝ) ≤ 1600 :=
      log_natCast_le_natCast (by norm_num)
    nlinarith
  have hlogSmall :
      Real.log ((200 * max rank 1 : ℕ) : ℝ) ≤
        200 + 6881393 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show ((200 * max rank 1 : ℕ) : ℝ) =
        (200 : ℝ) * ((max rank 1 : ℕ) : ℝ) by norm_num]
    rw [Real.log_mul (by norm_num) hmaxPosR.ne']
    have h200 : Real.log (200 : ℝ) ≤ 200 :=
      log_natCast_le_natCast (by norm_num)
    nlinarith
  have hEtaPos : 0 < 1600 * max rank 1 := by positivity
  have hSmallPos : 0 < 200 * max rank 1 := by positivity
  have hlog3Eta := log_three_mul_le_of_log_le hEtaPos hlogEta
  have hlog3Small := log_three_mul_le_of_log_le hSmallPos hlogSmall
  have hfactorEta :
      Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) + Real.log 4 ≤
        6882998 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hfactorSmall :
      Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) + Real.log 4 ≤
        6881598 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [log_four_le_two]
  have hrankR : (rank : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    calc
      (rank : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by simpa [R] using hrank)
      _ ≤ (1024 * dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 9 := by
        simpa [R] using (show
          (ConcreteNumerics.rankCap d (dyadicRankCost d) : ℝ) ≤
            (1024 * dyadicRankDegreeEightConstant : ℕ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 by
          exact_mod_cast dyadicRankCap_le_degree_nine d)
  have hfactorEtaNonneg :
      0 ≤ Real.log ((3 * (1600 * max rank 1) : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * (1600 * max rank 1) : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * (1600 * max rank 1) by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  have hfactorSmallNonneg :
      0 ≤ Real.log ((3 * (200 * max rank 1) : ℕ) : ℝ) + Real.log 4 := by
    have h3 : (1 : ℝ) ≤ (3 * (200 * max rank 1) : ℕ) := by
      exact_mod_cast (show 1 ≤ 3 * (200 * max rank 1) by omega)
    nlinarith [Real.log_nonneg h3, Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  rw [log_smoothingHierarchyLossFormula]
  have htermEta := mul_le_mul hrankR hfactorEta hfactorEtaNonneg (by positivity)
  have htermSmall := mul_le_mul hrankR hfactorSmall hfactorSmallNonneg (by positivity)
  push_cast at htermEta htermSmall ⊢
  nlinarith

/-- Formula-level product of every finite loss used in the final raw
high-norm branch.  ConcreteSupply unfolds its names to this expression. -/
def dyadicTotalLossFormula (d rank cap : ℕ) : ℕ :=
  twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne d (dyadicRankCost d))
      (ConcreteNumerics.mTwo d (dyadicRankCost d)) *
    smoothingHierarchyLossFormula rank *
      (3 * sourceDenominator rank cap
        (dyadicHierarchyFormula d
          (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank *
        dyadicCellMultiplier d

def dyadicTotalLogConstant : ℕ :=
  1024 * dyadicRankDegreeEightConstant * 57669725 +
    dyadicCellLogConstant

/-- The fixed dyadic cell multiplier has a degree-ten logarithmic loss.  This
is the main quantitative input for a uniform `cardMultiplier` in the final
raw supply. -/
lemma log_dyadicCellMultiplier_le_degree_ten (d : ℕ) :
    Real.log (dyadicCellMultiplier d : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 10 := by
  let R := ConcreteNumerics.rankCap d (dyadicRankCost d)
  let delta := dyadicRankCost d
  let n := dyadicQQuant d * (8 * dyadicRankCost d + 1)
  have hqPos : 0 < dyadicQQuant d := by
    unfold dyadicQQuant
    exact qQuant_pos (dyadicSiftedAlpha_pos d)
  have hdeltaPos : 0 < delta := by
    simpa [delta] using dyadicRankCost_pos d
  have hn : 0 < n := by
    unfold n
    positivity
  have hlogn : Real.log (n : ℝ) ≤
      8601726 * ((d + 1 : ℕ) : ℝ) ^ 2 := by
    simpa [n] using log_dyadicSampleBase_le_degree_two d
  have hlognNonneg : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n by exact Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hdelta : (delta : ℝ) ≤
      (dyadicRankDegreeEightConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 8 := by
    unfold delta
    exact_mod_cast dyadicRankCost_le_degree_eight d
  have hR : (R : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 9 := by
    unfold R
    exact_mod_cast dyadicRankCap_le_degree_nine d
  have hx : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ d + 1 by omega)
  have hpow8 : ((d + 1 : ℕ) : ℝ) ^ 8 ≤
      ((d + 1 : ℕ) : ℝ) ^ 10 :=
    pow_le_pow_right₀ hx (by omega)
  have hpow9 : ((d + 1 : ℕ) : ℝ) ^ 9 ≤
      ((d + 1 : ℕ) : ℝ) ^ 10 :=
    pow_le_pow_right₀ hx (by omega)
  have hfirst :
      (delta : ℝ) * Real.log (n : ℝ) ≤
        ((dyadicRankDegreeEightConstant : ℝ) * 8601726) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (delta : ℝ) * Real.log (n : ℝ) ≤
          ((dyadicRankDegreeEightConstant : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 8) *
            (8601726 * ((d + 1 : ℕ) : ℝ) ^ 2) :=
        mul_le_mul hdelta hlogn hlognNonneg (by positivity)
      _ = ((dyadicRankDegreeEightConstant : ℝ) * 8601726) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by ring
  have hsum10 : (R + delta : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant +
        dyadicRankDegreeEightConstant : ℕ) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (R : ℝ) + delta ≤
          ((1024 * dyadicRankDegreeEightConstant : ℕ) : ℝ) *
              ((d + 1 : ℕ) : ℝ) ^ 9 +
            dyadicRankDegreeEightConstant *
              ((d + 1 : ℕ) : ℝ) ^ 8 := add_le_add hR hdelta
      _ ≤ ((1024 * dyadicRankDegreeEightConstant : ℕ) : ℝ) *
              ((d + 1 : ℕ) : ℝ) ^ 10 +
            dyadicRankDegreeEightConstant *
              ((d + 1 : ℕ) : ℝ) ^ 10 := by
        gcongr
      _ = ((1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant : ℕ) : ℝ) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
        push_cast
        ring
  have hlogfour : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left log_two_le_one
      (show (0 : ℝ) ≤ 2 by norm_num)
    norm_num at hmul ⊢
    exact hmul
  have hlogfourNonneg : 0 ≤ Real.log (4 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hsecond :
      (R + delta : ℝ) * Real.log 4 ≤
        (2 : ℝ) *
          (1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
    calc
      (R + delta : ℝ) * Real.log 4 ≤
          ((1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant : ℕ) : ℝ) *
            ((d + 1 : ℕ) : ℝ) ^ 10 * 2 :=
        mul_le_mul hsum10 hlogfour hlogfourNonneg (by positivity)
      _ = (2 : ℝ) *
          (1024 * dyadicRankDegreeEightConstant +
            dyadicRankDegreeEightConstant) *
          ((d + 1 : ℕ) : ℝ) ^ 10 := by
        push_cast
        ring
  unfold dyadicCellMultiplier
  change Real.log (cellMultiplier R delta n : ℝ) ≤ _
  rw [log_cellMultiplier hn]
  unfold dyadicCellLogConstant
  push_cast at hfirst hsecond ⊢
  nlinarith

/-- One fixed degree-eleven logarithmic envelope for all global, hierarchy,
source, and localized-cell cardinality losses. -/
lemma log_dyadicTotalLossFormula_le_degree_eleven
    (d rank cap : ℕ)
    (hrank : rank ≤
      ConcreteNumerics.rankCap d (dyadicRankCost d))
    (hcap : cap ≤ 8 * dyadicRankCost d) :
    Real.log (dyadicTotalLossFormula d rank cap : ℝ) ≤
      (dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let two := twoReciprocalLossFormula rank
    (ConcreteNumerics.mOne d (dyadicRankCost d))
    (ConcreteNumerics.mTwo d (dyadicRankCost d))
  let smooth := smoothingHierarchyLossFormula rank
  let source :=
    (3 * sourceDenominator rank cap
      (dyadicHierarchyFormula d
        (ConcreteNumerics.rankCap d (dyadicRankCost d)))) ^ rank
  let cell := dyadicCellMultiplier d
  have htwo : Real.log (two : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 14658798 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [two] using
      log_twoReciprocalLossFormula_dyadic_le_degree_eleven d rank hrank
  have hsmooth : Real.log (smooth : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 20646194 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [smooth] using
      log_smoothingHierarchyLossFormula_dyadic_le_degree_eleven d rank hrank
  have hsource : Real.log (source : ℝ) ≤
      (1024 * dyadicRankDegreeEightConstant * 22364733 : ℕ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
    simpa [source] using
      log_sourcePow_dyadicFormula_le_degree_eleven d rank cap hrank hcap
  have hcell : Real.log (cell : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 10 := by
    simpa [cell] using log_dyadicCellMultiplier_le_degree_ten d
  have hx : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ d + 1 by omega)
  have hpow10 : ((d + 1 : ℕ) : ℝ) ^ 10 ≤
      ((d + 1 : ℕ) : ℝ) ^ 11 :=
    pow_le_pow_right₀ hx (by omega)
  have hcell11 : Real.log (cell : ℝ) ≤
      (dyadicCellLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 :=
    hcell.trans (mul_le_mul_of_nonneg_left hpow10 (by positivity))
  have htwoPos : (0 : ℝ) < two := by
    have hmOne := ConcreteNumerics.mOne_pos (d := d)
      (rankCost := dyadicRankCost d) (dyadicRankCost_pos d)
    have hmTwo := ConcreteNumerics.mTwo_pos (d := d)
      (rankCost := dyadicRankCost d) (dyadicRankCost_pos d)
    unfold two twoReciprocalLossFormula
    exact_mod_cast Nat.mul_pos
      (reciprocalLossFormula_pos hmOne) (reciprocalLossFormula_pos hmTwo)
  have hsmoothPos : (0 : ℝ) < smooth := by
    unfold smooth smoothingHierarchyLossFormula reciprocalLossFormula
    positivity
  have hsourcePos : (0 : ℝ) < source := by
    unfold source sourceDenominator dyadicHierarchyFormula
    positivity
  have hcellPos : (0 : ℝ) < cell := by
    have hq : 0 < dyadicQQuant d := by
      unfold dyadicQQuant
      exact qQuant_pos (dyadicSiftedAlpha_pos d)
    unfold cell dyadicCellMultiplier cellMultiplier
    positivity
  change Real.log ((two * smooth * source * cell : ℕ) : ℝ) ≤ _
  push_cast
  rw [Real.log_mul
      (mul_ne_zero
        (mul_ne_zero htwoPos.ne' hsmoothPos.ne') hsourcePos.ne')
      hcellPos.ne',
    Real.log_mul (mul_ne_zero htwoPos.ne' hsmoothPos.ne') hsourcePos.ne',
    Real.log_mul htwoPos.ne' hsmoothPos.ne']
  unfold dyadicTotalLogConstant
  push_cast at htwo hsmooth hsource hcell11 ⊢
  nlinarith

end

end RawSupplyNumerics

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140/ConcreteSupply.lean` -/

section
/-!
# Rank-regular concrete supply for the terminal step

This file deliberately avoids the plateau narrowing package: that package
remembers an exact plateau identity, whereas the quantitative Bourgain
alternative only needs a rank-regular unit carrier.  The lemmas here keep the
actual Bohr data and actual finite carriers visible.

The first part is unconditional geometry.  Starting with a rank-regular
unit-carrier restriction and a reciprocal scale, we regularize the small
dilate and obtain a genuine regular child, with the explicit
(3m)^rank * 4^rank cardinality loss.  The same child can be used twice in
the two-scale Bourgain alternative.

The second part records the exact remaining numerical hypotheses needed to
turn that geometry into a controlled increment.  They are inequalities about
the chosen reciprocal scale and the exponential budget, not a restatement of
the desired density-increment conclusion.
-/

open _root_.Finset Fintype _root_.Function
open scoped BigOperators _root_.NNReal Pointwise translate Indicator

namespace ConcreteSupply

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Transport commutes with scalar dilation. -/
theorem map_dilate_eq
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) (rho : NNReal) :
    (B.map e).dilate rho = (B.dilate rho).map e := by
  rfl

/-- Rank regularity is invariant under an additive equivalence.  In
particular this supplies regularity of the doubled middle carrier in odd
cyclic groups. -/
theorem isRankRegular_map
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (B : BohrData G) (e : G ≃+ H) (hB : B.IsRankRegular) :
    (B.map e).IsRankRegular := by
  unfold BohrData.IsRankRegular at hB ⊢
  simp only [BohrData.rank_map]
  intro kappa hkappa
  have h := hB kappa hkappa
  rw [map_dilate_eq, map_dilate_eq,
    BohrData.card_map_carrier, BohrData.card_map_carrier,
    BohrData.card_map_carrier]
  exact h

/-- The doubled Bohr datum in an odd cyclic group is rank regular whenever
the original datum is. -/
theorem doubledBohrData_rankRegular
    {M : ℕ} [NeZero M] (hM : Odd M) (B : BohrData (ZMod M))
    (hB : B.IsRankRegular) :
    (GroupCount.doubledBohrData M hM B).IsRankRegular := by
  exact isRankRegular_map B (BohrData.zmodDoublingEquiv M hM) hB

/-- A regular child obtained from a reciprocal scalar dilate.  The natural
cardinality inequality is the exact combination of arbitrary-scale Bohr
volume and the rank-regular subdatum loss. -/
theorem exists_rankRegular_child_inside_inv_dilate
    (B : BohrData G) (m : ℕ) (hm : 0 < m) :
    ∃ c : DensityStep.RegularChild (G := G),
      c.bohr.IsRankRegular ∧
      c.bohr.rank = B.rank ∧
      c.outer = 1 ∧
      c.carrier = c.bohr.carrier ∧
      c.carrier ⊆ (B.dilate ((m : NNReal)⁻¹)).carrier ∧
      B.carrier.card ≤
        ((3 * m) ^ B.rank * 4 ^ B.rank) * c.carrier.card := by
  classical
  let D := B.dilate ((m : NNReal)⁻¹)
  obtain ⟨R, hRreg, hRrank, hRD, hDcard⟩ :=
    LocalizedAlmostPeriodicity.exists_rankRegular_subdatum D
  obtain ⟨c, hcbohr, _hcouter, hccarrier⟩ :=
    DensityStep.RegularChild.exists_of_rankRegular R hRreg
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hcbohr] using hRreg
  · simpa [hcbohr, D] using hRrank
  · exact _hcouter
  · simpa [hcbohr] using hccarrier
  · simpa [hccarrier, D] using hRD
  · have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div
        B 1 hm
    have hscale' :
        B.carrier.card ≤
          (3 * m) ^ B.rank *
            (B.dilate ((m : NNReal)⁻¹)).carrier.card := by
      simpa [div_eq_mul_inv] using hscale
    calc
      B.carrier.card ≤
          (3 * m) ^ B.rank *
            (B.dilate ((m : NNReal)⁻¹)).carrier.card := hscale'
      _ ≤ (3 * m) ^ B.rank * (4 ^ B.rank * R.carrier.card) := by
        exact Nat.mul_le_mul_left _ (by simpa [D] using hDcard)
      _ = ((3 * m) ^ B.rank * 4 ^ B.rank) * c.carrier.card := by
        rw [hccarrier]
        ring

/-- The finite loss of one reciprocal-scale regularized child. -/
def reciprocalLoss (B : BohrData G) (m : ℕ) : ℕ :=
  (3 * m) ^ B.rank * 4 ^ B.rank

/-- The finite loss of first choosing K from B and then B' from K. -/
def twoReciprocalLoss (B : BohrData G) (mOne mTwo : ℕ) : ℕ :=
  reciprocalLoss B mOne * reciprocalLoss B mTwo

/-- Two actual children at two reciprocal scales.  The first child is the
baseline carrier K.  The second is constructed inside a further reciprocal
dilate of K, so its double is visibly contained in the Holder-small dilate
of K.  This is the geometry needed by the cross-term approximation; using
the same child twice would lose precisely this inclusion. -/
structure ReciprocalChildren (B : BohrData G) (mOne mTwo : ℕ) where
  childOne : DensityStep.RegularChild (G := G)
  childTwo : DensityStep.RegularChild (G := G)
  childOne_rankRegular : childOne.bohr.IsRankRegular
  childTwo_rankRegular : childTwo.bohr.IsRankRegular
  rankOne : childOne.bohr.rank = B.rank
  rankTwo : childTwo.bohr.rank = B.rank
  childOne_outer_one : childOne.outer = 1
  childTwo_outer_one : childTwo.outer = 1
  childOne_carrier : childOne.carrier = childOne.bohr.carrier
  childTwo_carrier : childTwo.carrier = childTwo.bohr.carrier
  smallOne : childOne.carrier ⊆ (B.dilate ((mOne : NNReal)⁻¹)).carrier
  smallTwo : childTwo.carrier ⊆ (B.dilate ((mOne : NNReal)⁻¹)).carrier
  middle_small :
    childTwo.carrier ⊆
      (childOne.bohr.dilate ((mTwo : NNReal)⁻¹)).carrier
  doubled_middle_small :
    GroupCount.doubledFinset childTwo.carrier ⊆
      (childOne.bohr.dilate
        ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier
  cardOne :
    B.carrier.card ≤
      reciprocalLoss B mOne * childOne.carrier.card
  cardTwo :
    B.carrier.card ≤
      twoReciprocalLoss B mOne mTwo * childTwo.carrier.card

/-- Unconditional construction of the two-scale geometry.  The only extra
input says that the second reciprocal scale is at most one; this is the
literal inclusion needed to regard the middle child as small for the
original Bourgain step as well as for Holder. -/
theorem exists_reciprocalChildren (B : BohrData G)
    (mOne mTwo : ℕ) (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (hmTwoInv : ((mTwo : NNReal)⁻¹) ≤ 1) :
    Nonempty (ReciprocalChildren B mOne mTwo) := by
  obtain ⟨cOne, hregOne, hrankOne, houterOne, hcarrierOne, hsmallOne, hcardOne⟩ :=
    exists_rankRegular_child_inside_inv_dilate B mOne hmOne
  obtain ⟨cTwo, hregTwo, hrankTwo', houterTwo, hcarrierTwo, hmiddle, hcardMiddle⟩ :=
    exists_rankRegular_child_inside_inv_dilate cOne.bohr mTwo hmTwo
  have hsmallTwo : cTwo.carrier ⊆
      (B.dilate ((mOne : NNReal)⁻¹)).carrier := by
    intro x hx
    apply hsmallOne
    rw [hcarrierOne]
    simpa using BohrData.carrier_dilate_mono hmTwoInv (hmiddle hx)
  have hdoubled :
      GroupCount.doubledFinset cTwo.carrier ⊆
        (cOne.bohr.dilate
          ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := GroupCount.mem_doubledFinset.mp hx
    exact BohrData.add_mem_dilate (hmiddle hy) (hmiddle hy)
  have hrankTwo : cTwo.bohr.rank = B.rank := hrankTwo'.trans hrankOne
  have hcardTwo :
      B.carrier.card ≤
        twoReciprocalLoss B mOne mTwo * cTwo.carrier.card := by
    calc
      B.carrier.card ≤
          reciprocalLoss B mOne * cOne.carrier.card :=
        hcardOne
      _ ≤ reciprocalLoss B mOne *
          (reciprocalLoss cOne.bohr mTwo *
            cTwo.carrier.card) :=
        Nat.mul_le_mul_left _
          (by simpa [hcarrierOne, reciprocalLoss] using hcardMiddle)
      _ = twoReciprocalLoss B mOne mTwo * cTwo.carrier.card := by
        simp [reciprocalLoss, twoReciprocalLoss, hrankOne]
        ring
  exact ⟨{
    childOne := cOne
    childTwo := cTwo
    childOne_rankRegular := hregOne
    childTwo_rankRegular := hregTwo
    rankOne := hrankOne
    rankTwo := hrankTwo
    childOne_outer_one := houterOne
    childTwo_outer_one := houterTwo
    childOne_carrier := hcarrierOne
    childTwo_carrier := hcarrierTwo
    smallOne := hsmallOne
    smallTwo := hsmallTwo
    middle_small := hmiddle
    doubled_middle_small := hdoubled
    cardOne := hcardOne
    cardTwo := hcardTwo }⟩

/-- Exact arithmetic facts needed to use reciprocal children as one
quantitative Bourgain step.  These are the genuine outstanding numerical
inequalities: scale smallness for rank regularity, scale smallness relative
to density, and conversion of the explicit finite volume loss to the chosen
exponential budget. -/
structure ReciprocalStepBounds {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (mOne mTwo : ℕ)
    (epsilon sizeCost : ℝ) where
  outer_eq_one : s.restriction.outer = 1
  rankRegular : s.restriction.bohr.IsRankRegular
  scale_rank :
    ((mOne : NNReal)⁻¹) ≤
      1 / (100 * (max s.restriction.bohr.rank 1 : ℕ) : NNReal)
  scale_density :
    400 * ((max s.restriction.bohr.rank 1 : ℕ) : ℝ) *
        (((mOne : NNReal)⁻¹ : NNReal) : ℝ) ≤ epsilon * s.density / 4
  card_budget_one :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      ((reciprocalLoss s.restriction.bohr mOne : ℕ) : ℝ)⁻¹ *
        (s.restriction.bohr.carrier.card : ℝ)
  card_budget_two :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      ((twoReciprocalLoss s.restriction.bohr mOne mTwo : ℕ) : ℝ)⁻¹ *
        (s.restriction.bohr.carrier.card : ℝ)

/-- A finite loss inequality and the corresponding reciprocal exponential
budget imply the actual child-cardinality bound.  This adapter is shared by
the raw Bourgain dichotomy above and the exact FinalAssembly interface below. -/
theorem child_card_of_loss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {loss : ℕ} {sizeCost : ℝ} {child : Finset G}
    (hloss : (0 : ℝ) < (loss : ℝ))
    (hbudget :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤
        (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ))
    (hvol :
      (s.restriction.bohr.carrier.card : ℝ) ≤
        (loss : ℝ) * (child.card : ℝ)) :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ child.card := by
  calc
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
        (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ) := hbudget
    _ ≤ (loss : ℝ)⁻¹ * ((loss : ℝ) * (child.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hvol (by positivity)
    _ = child.card := by
      field_simp

/-- A logarithmic loss bound is the exact scalar condition behind a
ReciprocalStepBounds cardinality field.  This removes exponentials from the
later coarse numerical bookkeeping. -/
theorem card_budget_of_log_loss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (houter : s.restriction.outer = 1)
    {loss : ℕ} {sizeCost : ℝ}
    (hloss : (0 : ℝ) < (loss : ℝ))
    (hlog : Real.log (loss : ℝ) ≤ sizeCost) :
    Real.exp (-sizeCost) * (s.card : ℝ) ≤
      (loss : ℝ)⁻¹ * (s.restriction.bohr.carrier.card : ℝ) := by
  have hexp :
      Real.exp (-sizeCost) ≤ (loss : ℝ)⁻¹ := by
    have hneg : -sizeCost ≤ -Real.log (loss : ℝ) := neg_le_neg hlog
    have h := Real.exp_le_exp.mpr hneg
    calc
      Real.exp (-sizeCost) ≤ Real.exp (-Real.log (loss : ℝ)) := h
      _ = (loss : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hloss]
  have hcard :
      (s.card : ℝ) = (s.restriction.bohr.carrier.card : ℝ) := by
    unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
      BohrStopping.RegularRestriction.ambient
    simp [houter]
  rw [hcard]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- Scalar form of the same logarithmic budget, used for a product of the
geometric and localized finite losses. -/
theorem exp_mul_loss_le_one_of_log_loss
    {loss : ℕ} {sizeCost : ℝ} (hloss : 0 < loss)
    (hlog : Real.log (loss : ℝ) ≤ sizeCost) :
    Real.exp (-sizeCost) * (loss : ℝ) ≤ 1 := by
  have hexp : Real.exp (-sizeCost) ≤ (loss : ℝ)⁻¹ := by
    have hneg : -sizeCost ≤ -Real.log (loss : ℝ) := neg_le_neg hlog
    calc
      Real.exp (-sizeCost) ≤ Real.exp (-Real.log (loss : ℝ)) :=
        Real.exp_le_exp.mpr hneg
      _ = (loss : ℝ)⁻¹ := by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast hloss)]
  calc
    Real.exp (-sizeCost) * (loss : ℝ) ≤ (loss : ℝ)⁻¹ * loss := by gcongr
    _ = 1 := by
      have hlossR : (0 : ℝ) < loss := by exact_mod_cast hloss
      field_simp

/-- Croot--Sisask lower bound with a large carrier for the sampled set and
a smaller carrier for the translating set.

This is the local estimate needed by the relative-T theorem.  If A has
density alpha in a large carrier D and A+S has at most C times the size of
D, then the sampled set has density at least (alpha/C)^k / 2 inside S.
Unlike an ambient-group estimate, this bound has no current-rank factor. -/
theorem croot_beta_mul_card_le_of_two_carriers
    {A S T D : Finset G} (k : ℕ) {alpha C : ℝ}
    (halpha : 0 ≤ alpha) (hC : 0 < C)
    (hA : A.Nonempty) (hS : S.Nonempty)
    (hAdense : alpha * (D.card : ℝ) ≤ (A.card : ℝ))
    (hsum : ((A + S).card : ℝ) ≤ C * (D.card : ℝ))
    (hT :
      (((A.card : ℝ) ^ k / 2 * S.card) /
          ((A + S).card : ℝ) ^ k ≤ (T.card : ℝ))) :
    (((alpha / C) ^ k / 2) * (S.card : ℝ)) ≤ (T.card : ℝ) := by
  have hsumPos : (0 : ℝ) < (A + S).card := by
    exact_mod_cast (hA.add hS).card_pos
  have hdenPos : (0 : ℝ) < ((A + S).card : ℝ) ^ k := by
    positivity
  apply le_trans ?_ hT
  apply (le_div_iff₀ hdenPos).2
  calc
    ((alpha / C) ^ k / 2) * (S.card : ℝ) *
        ((A + S).card : ℝ) ^ k ≤
      ((alpha / C) ^ k / 2) * (S.card : ℝ) *
        (C * (D.card : ℝ)) ^ k := by
          gcongr
    _ = (alpha * (D.card : ℝ)) ^ k / 2 * S.card := by
          have hCne : C ≠ 0 := hC.ne'
          rw [mul_pow]
          field_simp
          have hcancel : alpha / C * C = alpha := by field_simp
          rw [← mul_pow (alpha / C) C, hcancel, ← mul_pow]
    _ ≤ (A.card : ℝ) ^ k / 2 * S.card := by
          gcongr

/-- A set in the unit carrier plus a set in a small dilate stays in the
corresponding slight outer dilate.  The negated form is exactly the sumset
appearing in the relative-T Croot denominator. -/
theorem neg_add_small_subset_outer_dilate
    (B : BohrData G) (A S : Finset G) {rho : NNReal}
    (hA : A ⊆ B.carrier)
    (hS : S ⊆ (B.dilate rho).carrier) :
    (-A) + S ⊆ (B.dilate (1 + rho)).carrier := by
  intro x hx
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_neg.mp hu
  exact BohrData.add_mem_dilate
    (by simpa using (BohrData.neg_mem_carrier.mpr (hA ha))) (hS hv)

/-- Rank regularity makes a unit carrier plus a sufficiently small carrier
cost at most a factor two.  This is the local doubling estimate used before
the relative-T Chang bound. -/
theorem card_neg_add_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (A S : Finset G) {rho : NNReal}
    (hA : A ⊆ B.carrier)
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal)) :
    (-A + S).card ≤ 2 * B.carrier.card := by
  have hsub := neg_add_small_subset_outer_dilate B A S hA hS
  have hcard :
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
        (1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ)) *
          (B.carrier.card : ℝ) :=
    (hBreg rho hrho).2
  have hcoeff :
      1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤ 2 := by
    have hrhoReal :
        (rho : ℝ) ≤
          1 / (100 * ((max B.rank 1 : ℕ) : ℝ)) := by
      exact_mod_cast hrho
    have hrankPos : (0 : ℝ) < (max B.rank 1 : ℕ) := by positivity
    have hmul :
        100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤ 1 := by
      calc
        100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ) ≤
            100 * ((max B.rank 1 : ℕ) : ℝ) *
              (1 / (100 * ((max B.rank 1 : ℕ) : ℝ))) := by
                gcongr
        _ = 1 := by field_simp
    nlinarith
  have hcard' :
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
        2 * (B.carrier.card : ℝ) := by
    calc
      ((B.dilate (1 + rho)).carrier.card : ℝ) ≤
          (1 + 100 * ((max B.rank 1 : ℕ) : ℝ) * (rho : ℝ)) *
            (B.carrier.card : ℝ) := hcard
      _ ≤ 2 * (B.carrier.card : ℝ) := by
        gcongr
  have hsubCard :
      ((-A + S).card : ℝ) ≤
        ((B.dilate (1 + rho)).carrier.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact_mod_cast hsubCard.trans hcard'

/-- The same factor-two local-doubling estimate in the subtraction
orientation used by the supported popular set. -/
theorem card_sub_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (S : Finset G) {rho : NNReal}
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal)) :
    (B.carrier - S).card ≤ 2 * B.carrier.card := by
  have h :=
    card_neg_add_small_le_two_mul_card B hBreg B.carrier S
      (fun _ hx ↦ hx) hS hrho
  have hneg :
      (B.carrier - S).card = (-B.carrier + S).card := by
    rw [← Finset.card_neg]
    simp [sub_eq_add_neg, add_comm]
  rw [hneg]
  exact h

/-- Translating the large carrier does not change the local factor-two
difference-set bound. -/
theorem card_vadd_sub_small_le_two_mul_card
    (B : BohrData G) (hBreg : B.IsRankRegular)
    (S : Finset G) {rho : NNReal}
    (hS : S ⊆ (B.dilate rho).carrier)
    (hrho :
      rho ≤ 1 / (100 * (max B.rank 1 : ℕ) : NNReal))
    (z : G) :
    ((z +ᵥ B.carrier) - S).card ≤ 2 * B.carrier.card := by
  have hbase := card_sub_small_le_two_mul_card B hBreg S hS hrho
  have heq :
      (z +ᵥ B.carrier) - S = z +ᵥ (B.carrier - S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_vadd_finset.mp hu
      apply Finset.mem_vadd_finset.mpr
      exact ⟨b - v, Finset.mem_sub.mpr ⟨b, hb, v, hv, rfl⟩, by
        simp only [vadd_eq_add]
        abel⟩
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨b, hb, v, hv, rfl⟩ := Finset.mem_sub.mp hu
      apply Finset.mem_sub.mpr
      exact ⟨z + b, Finset.mem_vadd_finset.mpr ⟨b, hb, rfl⟩,
        v, hv, by
          simp only [vadd_eq_add]
          abel⟩
  rw [heq, Finset.card_vadd_finset]
  exact hbase

/-- Two regular carriers for the terminal smoothing measure.  The large
carrier D is a regular dilate inside a tiny dilate of the doubled middle
carrier W.  The sampling carrier E is a further tiny regular dilate of D.
Keeping the two regularizing scalars explicit is what makes both the local
sumset estimate and the final support inclusion available. -/
structure SmoothingHierarchy (W : BohrData G) where
  eta : NNReal
  Dbohr : BohrData G
  rhoD : NNReal
  theta : NNReal
  Ebohr : BohrData G
  rhoE : NNReal
  phi : NNReal
  B₀ : BohrData G
  rho₀ : NNReal
  eta_eq : eta = 1 / (1600 * (max W.rank 1 : ℕ) : NNReal)
  eta_pos : 0 < eta
  eta_narrow :
    4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : NNReal)
  D_eq : Dbohr = (W.dilate eta).dilate rhoD
  rhoD_half : 1 / 2 ≤ rhoD
  rhoD_one : rhoD ≤ 1
  D_regular : Dbohr.IsRankRegular
  theta_eq : theta = 1 / (200 * (max Dbohr.rank 1 : ℕ) : NNReal)
  theta_pos : 0 < theta
  theta_small :
    theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal)
  E_eq : Ebohr = (Dbohr.dilate theta).dilate rhoE
  rhoE_half : 1 / 2 ≤ rhoE
  rhoE_one : rhoE ≤ 1
  E_regular : Ebohr.IsRankRegular
  phi_eq : phi = 1 / (200 * (max Ebohr.rank 1 : ℕ) : NNReal)
  phi_pos : 0 < phi
  phi_small :
    phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal)
  B₀_eq : B₀ = (Ebohr.dilate phi).dilate rho₀
  rho₀_half : 1 / 2 ≤ rho₀
  rho₀_one : rho₀ ≤ 1
  B₀_regular : B₀.IsRankRegular
  D_small : Dbohr.carrier ⊆ (W.dilate eta).carrier
  E_small : Ebohr.carrier ⊆ (W.dilate eta).carrier
  E_in_Dtheta : Ebohr.carrier ⊆ (Dbohr.dilate theta).carrier
  B₀_small : B₀.carrier ⊆ (W.dilate eta).carrier
  B₀_in_Ephi : B₀.carrier ⊆ (Ebohr.dilate phi).carrier

/-- Unconditional two-scale smoothing hierarchy inside a rank-regular
doubled middle carrier.  The chosen constants are deliberately coarse:
eta pays the fourfold support expansion, and theta pays the local
factor-two sumset comparison. -/
theorem exists_smoothingHierarchy (W : BohrData G) :
    Nonempty (SmoothingHierarchy W) := by
  let dW : ℕ := max W.rank 1
  let eta : NNReal := 1 / (1600 * (dW : NNReal))
  have hdW : 0 < dW := by simp [dW]
  have hetaPos : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaNarrow :
      4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : NNReal) := by
    dsimp [eta, dW]
    have hd : (0 : NNReal) < (max W.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rhoD, hrhoDhalf, hrhoDone, hDreg⟩ :=
    (W.dilate eta).exists_rankRegular_dilate
  let Dbohr : BohrData G := (W.dilate eta).dilate rhoD
  let dD : ℕ := max Dbohr.rank 1
  let theta : NNReal := 1 / (200 * (dD : NNReal))
  have hdD : 0 < dD := by simp [dD]
  have hthetaPos : 0 < theta := by
    dsimp [theta]
    positivity
  have hthetaSmall :
      theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal) := by
    dsimp [theta, dD]
    have hd : (0 : NNReal) < (max Dbohr.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rhoE, hrhoEhalf, hrhoEone, hEreg⟩ :=
    (Dbohr.dilate theta).exists_rankRegular_dilate
  let Ebohr : BohrData G := (Dbohr.dilate theta).dilate rhoE
  let dE : ℕ := max Ebohr.rank 1
  let phi : NNReal := 1 / (200 * (dE : NNReal))
  have hdE : 0 < dE := by simp [dE]
  have hphiPos : 0 < phi := by
    dsimp [phi]
    positivity
  have hphiSmall :
      phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal) := by
    dsimp [phi, dE]
    have hd : (0 : NNReal) < (max Ebohr.rank 1 : ℕ) := by positivity
    field_simp
    norm_num
  obtain ⟨rho₀, hrho₀half, hrho₀one, hB₀reg⟩ :=
    (Ebohr.dilate phi).exists_rankRegular_dilate
  let B₀ : BohrData G := (Ebohr.dilate phi).dilate rho₀
  have hDsmall : Dbohr.carrier ⊆ (W.dilate eta).carrier := by
    dsimp [Dbohr]
    simpa using
      (BohrData.carrier_dilate_mono hrhoDone :
        ((W.dilate eta).dilate rhoD).carrier ⊆
          ((W.dilate eta).dilate 1).carrier)
  have hEtheta :
      Ebohr.carrier ⊆ (Dbohr.dilate theta).carrier := by
    dsimp [Ebohr]
    simpa using
      (BohrData.carrier_dilate_mono hrhoEone :
        ((Dbohr.dilate theta).dilate rhoE).carrier ⊆
          ((Dbohr.dilate theta).dilate 1).carrier)
  have hthetaOne : theta ≤ 1 := by
    calc
      theta ≤ 1 / (100 * (max Dbohr.rank 1 : ℕ) : NNReal) :=
        hthetaSmall
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 100 * max Dbohr.rank 1 by omega)
        · positivity
  have hEsmall : Ebohr.carrier ⊆ (W.dilate eta).carrier := by
    apply hEtheta.trans
    apply (BohrData.carrier_dilate_mono hthetaOne).trans
    simpa using hDsmall
  have hB₀phi :
      B₀.carrier ⊆ (Ebohr.dilate phi).carrier := by
    dsimp [B₀]
    simpa using
      (BohrData.carrier_dilate_mono hrho₀one :
        ((Ebohr.dilate phi).dilate rho₀).carrier ⊆
          ((Ebohr.dilate phi).dilate 1).carrier)
  have hphiOne : phi ≤ 1 := by
    calc
      phi ≤ 1 / (100 * (max Ebohr.rank 1 : ℕ) : NNReal) :=
        hphiSmall
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 100 * max Ebohr.rank 1 by omega)
        · positivity
  have hB₀small : B₀.carrier ⊆ (W.dilate eta).carrier := by
    apply hB₀phi.trans
    apply (BohrData.carrier_dilate_mono hphiOne).trans
    simpa using hEsmall
  exact ⟨{
    eta := eta
    Dbohr := Dbohr
    rhoD := rhoD
    theta := theta
    Ebohr := Ebohr
    rhoE := rhoE
    phi := phi
    B₀ := B₀
    rho₀ := rho₀
    eta_eq := rfl
    eta_pos := hetaPos
    eta_narrow := hetaNarrow
    D_eq := rfl
    rhoD_half := hrhoDhalf
    rhoD_one := hrhoDone
    D_regular := by simpa [Dbohr] using hDreg
    theta_eq := rfl
    theta_pos := hthetaPos
    theta_small := hthetaSmall
    E_eq := rfl
    rhoE_half := hrhoEhalf
    rhoE_one := hrhoEone
    E_regular := by simpa [Ebohr] using hEreg
    phi_eq := rfl
    phi_pos := hphiPos
    phi_small := hphiSmall
    B₀_eq := rfl
    rho₀_half := hrho₀half
    rho₀_one := hrho₀one
    B₀_regular := by simpa [B₀] using hB₀reg
    D_small := hDsmall
    E_small := hEsmall
    E_in_Dtheta := hEtheta
    B₀_small := hB₀small
    B₀_in_Ephi := hB₀phi }⟩

/-- Regularizing at a scale at least one half costs at most the standard
four-to-the-rank factor. -/
theorem card_le_four_pow_rank_mul_card_dilate_of_half_le
    (B : BohrData G) (rho : NNReal) (hrho : 1 / 2 ≤ rho) :
    B.carrier.card ≤ 4 ^ B.rank * (B.dilate rho).carrier.card := by
  have hhalf := B.card_unit_le_four_pow_rank_mul_card_half
  have hmono :
      (B.dilate (1 / 2)).carrier.card ≤ (B.dilate rho).carrier.card :=
    Finset.card_le_card (BohrData.carrier_dilate_mono hrho)
  calc
    B.carrier.card ≤ 4 ^ B.rank * (B.dilate (1 / 2)).carrier.card :=
      by simpa using hhalf
    _ ≤ 4 ^ B.rank * (B.dilate rho).carrier.card :=
      Nat.mul_le_mul_left _ hmono

/-- All three datums in the hierarchy retain the rank of the doubled
middle datum. -/
theorem smoothingHierarchy_ranks (W : BohrData G) (H : SmoothingHierarchy W) :
    H.Dbohr.rank = W.rank ∧ H.Ebohr.rank = W.rank ∧ H.B₀.rank = W.rank := by
  have hD : H.Dbohr.rank = W.rank := by
    rw [H.D_eq, BohrData.rank_dilate, BohrData.rank_dilate]
  have hE : H.Ebohr.rank = W.rank := by
    rw [H.E_eq, BohrData.rank_dilate, BohrData.rank_dilate]
    exact hD
  have hB : H.B₀.rank = W.rank := by
    rw [H.B₀_eq, BohrData.rank_dilate, BohrData.rank_dilate]
    exact hE
  constructor
  · exact hD
  constructor
  · exact hE
  · exact hB

/-- Explicit finite loss from the doubled middle carrier to the sampling
carrier.  The three factors are respectively the eta, theta, and phi
reciprocal dilates, each followed by a half-to-one regularization. -/
def smoothingHierarchyLoss (W : BohrData G) : ℕ :=
  ((3 * (1600 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
    ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
    ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank)

theorem smoothingHierarchy_card_loss
    (W : BohrData G) (H : SmoothingHierarchy W) :
    W.carrier.card ≤ smoothingHierarchyLoss W * H.B₀.carrier.card := by
  let Peta : ℕ := 1600 * max W.rank 1
  let Psmall : ℕ := 200 * max W.rank 1
  have hPeta : 0 < Peta := by dsimp [Peta]; positivity
  have hPsmall : 0 < Psmall := by dsimp [Psmall]; positivity
  have hranks := smoothingHierarchy_ranks W H
  have hWeta :
      W.carrier.card ≤ (3 * Peta) ^ W.rank *
        (W.dilate H.eta).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div W 1 hPeta
    rw [H.eta_eq]
    simpa [Peta, div_eq_mul_inv] using hscale
  have hEtaD :
      (W.dilate H.eta).carrier.card ≤ 4 ^ W.rank * H.Dbohr.carrier.card := by
    rw [H.D_eq]
    simpa only [BohrData.rank_dilate] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (W.dilate H.eta) H.rhoD H.rhoD_half
  have hDEbase :
      H.Dbohr.carrier.card ≤ (3 * Psmall) ^ W.rank *
        (H.Dbohr.dilate H.theta).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div H.Dbohr 1 hPsmall
    rw [H.theta_eq]
    simpa [Psmall, hranks.1, div_eq_mul_inv] using hscale
  have hbaseE :
      (H.Dbohr.dilate H.theta).carrier.card ≤
        4 ^ W.rank * H.Ebohr.carrier.card := by
    rw [H.E_eq]
    simpa [hranks.1] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (H.Dbohr.dilate H.theta) H.rhoE H.rhoE_half
  have hEBbase :
      H.Ebohr.carrier.card ≤ (3 * Psmall) ^ W.rank *
        (H.Ebohr.dilate H.phi).carrier.card := by
    have hscale :=
      BohrData.card_dilate_le_three_mul_pow_rank_mul_card_div H.Ebohr 1 hPsmall
    rw [H.phi_eq]
    simpa [Psmall, hranks.2.1, div_eq_mul_inv] using hscale
  have hbaseB :
      (H.Ebohr.dilate H.phi).carrier.card ≤
        4 ^ W.rank * H.B₀.carrier.card := by
    rw [H.B₀_eq]
    simpa [hranks.2.1] using
      card_le_four_pow_rank_mul_card_dilate_of_half_le
        (H.Ebohr.dilate H.phi) H.rho₀ H.rho₀_half
  unfold smoothingHierarchyLoss
  calc
    W.carrier.card ≤ (3 * Peta) ^ W.rank *
        (W.dilate H.eta).carrier.card := hWeta
    _ ≤ (3 * Peta) ^ W.rank * (4 ^ W.rank * H.Dbohr.carrier.card) :=
      Nat.mul_le_mul_left _ hEtaD
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        ((3 * Psmall) ^ W.rank *
          (H.Dbohr.dilate H.theta).carrier.card) := by
      have h := Nat.mul_le_mul_left
        ((3 * Peta) ^ W.rank * 4 ^ W.rank) hDEbase
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        ((3 * Psmall) ^ W.rank * (4 ^ W.rank * H.Ebohr.carrier.card)) := by
      gcongr
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        (((3 * Psmall) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank *
            (H.Ebohr.dilate H.phi).carrier.card)) := by
      have h := Nat.mul_le_mul_left
        (((3 * Peta) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank * 4 ^ W.rank)) hEBbase
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    _ ≤ ((3 * Peta) ^ W.rank * 4 ^ W.rank) *
        (((3 * Psmall) ^ W.rank * 4 ^ W.rank) *
          ((3 * Psmall) ^ W.rank * (4 ^ W.rank * H.B₀.carrier.card))) := by
      gcongr
    _ = (((3 * (1600 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
        ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank) *
        ((3 * (200 * max W.rank 1)) ^ W.rank * 4 ^ W.rank)) *
        H.B₀.carrier.card := by
      simp [Peta, Psmall]
      ring

/-- The autocorrelation of two sets in the same eta-dilate is supported in
the fourfold eta-dilate.  This is the only support calculation needed for
the two-Bohr smoothing weight. -/
theorem smoothingWeight_support_subset_four_dilate
    (W : BohrData G) {D E : Finset G} {eta : NNReal}
    (hD : D ⊆ (W.dilate eta).carrier)
    (hE : E ⊆ (W.dilate eta).carrier) :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (W.dilate (4 * eta)).carrier := by
  intro t ht
  have htSupport :
      t ∈ Function.support (LocalizedUnbalancing.smoothingWeight D E) := ht
  have hbaseNonneg :
      0 ≤ LocalizedUnbalancing.smoothingBase D E := by
    simp [LocalizedUnbalancing.smoothingBase]
  have htDiff : t ∈ (D + E) - (D + E) := by
    rw [LocalizedUnbalancing.smoothingWeight,
      support_dddconv hbaseNonneg hbaseNonneg,
      LocalizedUnbalancing.smoothingBase,
      support_ddconv mu_nonneg mu_nonneg,
      support_mu, support_mu] at htSupport
    simpa only [← coe_add, ← coe_sub, mem_coe] using htSupport
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp htDiff
  obtain ⟨d₁, hd₁, e₁, he₁, rfl⟩ := Finset.mem_add.mp hu
  obtain ⟨d₂, hd₂, e₂, he₂, rfl⟩ := Finset.mem_add.mp hv
  have hu' :
      d₁ + e₁ ∈ (W.dilate (eta + eta)).carrier :=
    BohrData.add_mem_dilate (hD hd₁) (hE he₁)
  have hv' :
      d₂ + e₂ ∈ (W.dilate (eta + eta)).carrier :=
    BohrData.add_mem_dilate (hD hd₂) (hE he₂)
  have hsub :
      (d₁ + e₁) - (d₂ + e₂) ∈
        (W.dilate ((eta + eta) + (eta + eta))).carrier :=
    BohrData.sub_mem_dilate hu' hv'
  simpa [show (eta + eta) + (eta + eta) = 4 * eta by ring] using hsub

/-- The hierarchy smoothing weight is supported inside the first child once
the doubled middle carrier is identified with its concrete doubled Bohr
datum.  This is the support field of the final raw endpoint package. -/
theorem smoothing_support_of_hierarchy_twoScale
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ}
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    (W : BohrData G) (H : SmoothingHierarchy W)
    (hWcarrier : W.carrier = GroupCount.doubledFinset C.childTwo.carrier) :
    ∀ t,
      LocalizedUnbalancing.smoothingWeight H.Ebohr.carrier H.Dbohr.carrier t ≠ 0 →
      t ∈ (C.childOne.bohr.dilate
        ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier := by
  intro t ht
  have htFour :
      t ∈ (W.dilate (4 * H.eta)).carrier :=
    smoothingWeight_support_subset_four_dilate W H.E_small H.D_small t ht
  have hfourOne : 4 * H.eta ≤ (1 : NNReal) := by
    calc
      4 * H.eta ≤
          1 / (400 * (max W.rank 1 : ℕ) : NNReal) := H.eta_narrow
      _ ≤ 1 := by
        rw [div_le_one]
        · exact_mod_cast (show 1 ≤ 400 * max W.rank 1 by omega)
        · positivity
  have htW : t ∈ W.carrier := by
    simpa only [BohrData.dilate_one] using
      (BohrData.carrier_dilate_mono hfourOne htFour)
  rw [hWcarrier] at htW
  exact C.doubled_middle_small htW

/-- The Croot sumset attached to the sampling carrier of a smoothing
hierarchy.  Naming it keeps the nested pointwise operations out of later
quantitative theorem signatures. -/
def hierarchyCrootSumset
    (W : BohrData G) (H : SmoothingHierarchy W) (A₂ : Finset G) : Finset G :=
  (-A₂) + H.B₀.carrier

def hierarchyCrootCard
    (W : BohrData G) (H : SmoothingHierarchy W) (A₂ : Finset G) : ℝ :=
  (hierarchyCrootSumset W H A₂).card

def hierarchySampleCard
    (W : BohrData G) (H : SmoothingHierarchy W) : ℝ :=
  H.B₀.carrier.card

def hierarchyNegCard (A₂ : Finset G) : ℝ :=
  (-A₂).card

section HierarchyRelativeT

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

def hierarchyBeta
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (_data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (k : ℕ) : ℝ :=
  ((DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p / 2) ^ k) / 2

/-- The three-level hierarchy turns the raw relative-T Croot lower bound
into a genuine density lower bound inside the sampling carrier B₀.

Here the large raw smoothing set is H.Dbohr and the small raw smoothing set
is H.Ebohr.  The sifting output A₂ lies in the small carrier, while B₀ lies
in a tiny phi-dilate of that carrier.  Rank regularity then bounds
|-A₂+B₀| by twice the small-carrier size, so the resulting beta has no
dependence on the current Bohr rank. -/
theorem hierarchy_relativeT_beta
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    ((((DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p / 2) ^ k) /
        2) * hierarchySampleCard W H) ≤ (T.card : ℝ) := by
  have houtputs := data.output_nonempty hdelta
  have hEcardPos : (0 : ℝ) < H.Ebohr.carrier.card := by
    exact_mod_cast H.Ebohr.carrier_nonempty.card_pos
  have hAdense :
      DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p *
          (H.Ebohr.carrier.card : ℝ) ≤ (data.A₂.card : ℝ) := by
    exact (le_div_iff₀ hEcardPos).mp data.density_two
  have hnegAdense :
      DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p *
          (H.Ebohr.carrier.card : ℝ) ≤ ((-data.A₂).card : ℝ) := by
    simpa using hAdense
  have hsumNat :
      (hierarchyCrootSumset W H data.A₂).card ≤
        2 * H.Ebohr.carrier.card := by
    unfold hierarchyCrootSumset
    apply card_neg_add_small_le_two_mul_card H.Ebohr H.E_regular
      data.A₂ (H.B₀).carrier data.subset_two H.B₀_in_Ephi H.phi_small
  have hsum :
      hierarchyCrootCard W H data.A₂ ≤
        2 * (H.Ebohr.carrier.card : ℝ) := by
    unfold hierarchyCrootCard
    exact_mod_cast hsumNat
  have halpha :
      0 ≤ DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p := by
    unfold DensityStep.siftingDensityLower
    positivity
  have hnegA : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  simpa only [hierarchyNegCard, hierarchySampleCard, hierarchyCrootCard,
    hierarchyCrootSumset, show (2 : ℝ) = 2 by rfl] using
    (croot_beta_mul_card_le_of_two_carriers
      (A := -data.A₂) (S := (H.B₀).carrier) (T := T)
      (D := H.Ebohr.carrier) k halpha (by norm_num : (0 : ℝ) < 2)
      hnegA (H.B₀).carrier_nonempty hnegAdense hsum hT)

/-- The same local Croot estimate gives the uniform natural-number rank
cap used by the localized package. -/
theorem hierarchy_delta_card_le_of_croot
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G) (Delta : Finset (AddChar G Complex))
    (hbeta : 0 <
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
        (delta := delta) W H data k)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)))
    (hDelta : (Delta.card : ℝ) ≤
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)) :
    Delta.card ≤
      ⌈8 * (1 + Real.log (2 /
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k))⌉₊ := by
  have hTbeta :
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k * (H.B₀.carrier.card : ℝ) ≤
        (T.card : ℝ) := by
    simpa [hierarchyBeta, hierarchySampleCard] using
      hierarchy_relativeT_beta W H data hdelta k T hT
  have hdim :
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
        8 * (1 + Real.log (2 /
          hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
            (delta := delta) W H data k)) :=
    localChangDimension_half_le_of_mul_card_le H.B₀ T hbeta
      (by
        have hpos : (0 : ℝ) <
            hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
              (delta := delta) W H data k *
            (H.B₀.carrier.card : ℝ) :=
          mul_pos hbeta (by exact_mod_cast H.B₀.carrier_nonempty.card_pos)
        have hTpos : (0 : ℝ) < T.card := hpos.trans_le hTbeta
        exact Finset.card_pos.mp (by exact_mod_cast hTpos))
      hTbeta
  exact card_le_natCeil_of_cast_card_le Delta (hDelta.trans hdim)

/-- The real-valued companion to the preceding cardinality bound.  This is
kept separate because the spectral quantizer depends on the Chang dimension
itself, not just on the cardinality of the chosen spectrum. -/
theorem hierarchy_dimension_le_of_croot
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (W : BohrData G) (H : SmoothingHierarchy W)
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (k : ℕ) (T : Finset G)
    (hbeta : 0 <
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
        (delta := delta) W H data k)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
      8 * (1 + Real.log (2 /
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k)) := by
  have hTbeta :
      hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
          (delta := delta) W H data k * (H.B₀.carrier.card : ℝ) ≤
        (T.card : ℝ) := by
    simpa [hierarchyBeta, hierarchySampleCard] using
      hierarchy_relativeT_beta W H data hdelta k T hT
  apply localChangDimension_half_le_of_mul_card_le H.B₀ T hbeta
  · have hpos : (0 : ℝ) <
        hierarchyBeta (A := A) (B₁ := B₁) (p := p) (sigma := sigma)
            (delta := delta) W H data k *
          (H.B₀.carrier.card : ℝ) :=
      mul_pos hbeta (by exact_mod_cast H.B₀.carrier_nonempty.card_pos)
    have hTpos : (0 : ℝ) < T.card := hpos.trans_le hTbeta
    exact Finset.card_pos.mp (by exact_mod_cast hTpos)
  · exact hTbeta

end HierarchyRelativeT

/-- The fixed Holder exponent 4(d+1) is already enough for the dense-pair
loss 1/512 on a dyadic-density state. -/
theorem densePairDensity_power_of_dyadic
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d : ℕ}
    (hscale : (1 / (2 : ℝ) ^ d) ≤ s.density) :
    (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤
      (1 - (1 / 512 : ℝ)) * s.density := by
  have hbase : (2 / 3 : ℝ) ^ 4 ≤ 1 / 2 := by norm_num
  have hpow :
      (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤ (1 / 2 : ℝ) ^ (d + 1) := by
    calc
      (2 / 3 : ℝ) ^ (4 * (d + 1)) =
          ((2 / 3 : ℝ) ^ 4) ^ (d + 1) := by rw [pow_mul]
      _ ≤ (1 / 2 : ℝ) ^ (d + 1) :=
        pow_le_pow_left₀ (by positivity) hbase (d + 1)
  have hdecay :
      (1 / 2 : ℝ) ^ (d + 1) ≤
        (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := by
    have hpowNonneg : 0 ≤ (1 / 2 : ℝ) ^ d := by positivity
    rw [pow_succ]
    calc
      (1 / 2 : ℝ) ^ d * (1 / 2) ≤
          (1 / 2 : ℝ) ^ d * (511 / 512) :=
        mul_le_mul_of_nonneg_left (by norm_num) hpowNonneg
      _ = (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := by
        simp [one_div, inv_pow, mul_comm]
  calc
    (2 / 3 : ℝ) ^ (4 * (d + 1)) ≤ (1 / 2 : ℝ) ^ (d + 1) := hpow
    _ ≤ (511 / 512 : ℝ) * (1 / (2 : ℝ) ^ d) := hdecay
    _ ≤ (511 / 512 : ℝ) * s.density :=
      mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = (1 - (1 / 512 : ℝ)) * s.density := by ring

/-- Convert the concrete two-scale children into the exact rank-regular
narrowing object consumed by FinalAssembly.RawConcreteSupply.  This is the
plateau-free geometry component of that final interface. -/
noncomputable def rankRegularNarrowingPackage_of_reciprocalChildren
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {epsilon sizeCost : ℝ} {rankCost : ℕ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo epsilon sizeCost) :
    FinalAssembly.RankRegularNarrowingPackage s epsilon sizeCost rankCost := by
  have hfactorOnePos :
      (0 : ℝ) < (reciprocalLoss s.located.restriction.bohr mOne : ℝ) := by
    unfold reciprocalLoss
    positivity
  have hfactorTwoPos :
      (0 : ℝ) <
        (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) := by
    unfold twoReciprocalLoss reciprocalLoss
    positivity
  have hvolOne :
      (s.located.restriction.bohr.carrier.card : ℝ) ≤
        (reciprocalLoss s.located.restriction.bohr mOne : ℝ) *
          (C.childOne.carrier.card : ℝ) := by
    exact_mod_cast C.cardOne
  have hvolTwo :
      (s.located.restriction.bohr.carrier.card : ℝ) ≤
        (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
          (C.childTwo.carrier.card : ℝ) := by
    exact_mod_cast C.cardTwo
  have hcardOne :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card := by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
      child_card_of_loss s.located hfactorOnePos hnum.card_budget_one hvolOne
  have hcardTwo :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ C.childTwo.carrier.card := by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
      child_card_of_loss s.located hfactorTwoPos hnum.card_budget_two hvolTwo
  have hdensityEq :
      relativeDensityOn s.located.restriction.set
          s.located.restriction.bohr.carrier = s.located.density := by
    unfold DensityStep.LocatedRestriction.density
      BohrStopping.RegularRestriction.density relativeDensityOn
      BohrStopping.RegularRestriction.ambient
    simp [s.outer_one]
  refine
    { kappa := (mOne : NNReal)⁻¹
      kappa_small := hnum.scale_rank
      childOne := C.childOne
      childTwo := C.childTwo
      childOne_outer_one := C.childOne_outer_one
      childTwo_outer_one := C.childTwo_outer_one
      childOne_rankRegular := C.childOne_rankRegular
      childTwo_rankRegular := C.childTwo_rankRegular
      smallOne := C.smallOne
      smallTwo := C.smallTwo
      narrowing_small := ?_
      rankOne := ?_
      rankTwo := ?_
      cardOne := hcardOne
      cardTwo := hcardTwo }
  · simpa only [hdensityEq] using hnum.scale_density
  · rw [C.rankOne]
    simp [FinalAssembly.RankRegularLocatedRestriction.rank,
      DensityStep.LocatedRestriction.rank, BohrStopping.RegularRestriction.rank]
  · rw [C.rankTwo]
    simp [FinalAssembly.RankRegularLocatedRestriction.rank,
      DensityStep.LocatedRestriction.rank, BohrStopping.RegularRestriction.rank]

/-! ## Plateau-free Holder fibres -/

/-- Endpoint fibre selected from a rank-regular dense pair. -/
def endpointSet {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childOne.carrier
    (GroupCount.densePairPoint hdense)

/-- Middle-term fibre selected from the same dense-pair point. -/
def middleSet {original : Finset G}
    (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) : Finset G :=
  DensityStep.narrowingSet s.restriction.set childTwo.carrier
    (GroupCount.densePairPoint hdense)

/-- The common density retained by a rank-regular dense pair. -/
def densePairDensity {original : Finset G}
    (s : DensityStep.LocatedRestriction original) (epsilon : ℝ) : ℝ :=
  (1 - epsilon) * s.density

/-- The selected endpoint fibre is nonempty whenever the dense-pair loss is
strictly below one.  This is the exact nonemptiness field of the final raw
two-Bohr package, factored out so the analytic construction never has to
replay the local-density argument. -/
theorem endpointSet_nonempty
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    (endpointSet s childOne childTwo hdense).Nonempty := by
  let alpha := densePairDensity s epsilon
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hOne : alpha ≤
      localDensity s.restriction.set childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
    childOne.carrier_nonempty
  exact halpha.trans_le hOne

/-- The selected endpoint fibre lies in the first actual child carrier. -/
theorem endpointSet_subset_childOne
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon) :
    endpointSet s childOne childTwo hdense ⊆ childOne.carrier := by
  exact DensityStep.narrowingSet_subset_carrier
    (B := childOne.bohr) (rho := childOne.outer)
    (A := s.restriction.set) (C := childOne.carrier)
    (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)

/-- The actual located restriction whose set is the endpoint fibre.  This is
the state on which the high-smoothing-norm theorem must run, so subsequent
cardinality losses compose honestly. -/
noncomputable def endpointLocated
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    DensityStep.LocatedRestriction original := by
  let x := GroupCount.densePairPoint hdense
  have hfactor : 0 < densePairDensity s epsilon :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hx : densePairDensity s epsilon ≤
      localDensity s.restriction.set childOne.carrier x := by
    simpa [x, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  exact DensityStep.narrowLocated s childOne x (hfactor.trans_le hx)

@[simp] theorem endpointLocated_set
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (childOne childTwo : DensityStep.RegularChild (G := G)) {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s childOne childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    (endpointLocated s childOne childTwo hdense hepsilon_lt_one).restriction.set =
      endpointSet s childOne childTwo hdense := by
  rfl

/-- The endpoint fibre is no larger than the current located state. -/
theorem endpointLocated_card_le_state_card
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne)
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (houter : s.restriction.outer = 1) :
    (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤ s.card := by
  have hmOneInv : ((mOne : NNReal)⁻¹) ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast hmOne)).2
    exact_mod_cast (show 1 ≤ mOne by omega)
  have hchild : C.childOne.carrier.card ≤ s.restriction.bohr.carrier.card := by
    calc
      C.childOne.carrier.card ≤
          (s.restriction.bohr.dilate ((mOne : NNReal)⁻¹)).carrier.card :=
        Finset.card_le_card C.smallOne
      _ ≤ (s.restriction.bohr.dilate 1).carrier.card :=
        Finset.card_le_card (BohrData.carrier_dilate_mono hmOneInv)
      _ = s.restriction.bohr.carrier.card := by simp
  calc
    (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card =
        C.childOne.carrier.card := by
      simp [endpointLocated, DensityStep.narrowLocated,
        DensityStep.RegularChild.asRestriction,
        DensityStep.LocatedRestriction.card, BohrStopping.RegularRestriction.card,
        BohrStopping.RegularRestriction.ambient, C.childOne_outer_one,
        C.childOne_carrier]
    _ ≤ s.restriction.bohr.carrier.card := hchild
    _ = s.card := by
      unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
        BohrStopping.RegularRestriction.ambient
      simp [houter]

/-- The whole two-scale/hierarchy geometry compares the endpoint fibre to
the final sampling carrier by one explicit finite loss. -/
theorem endpoint_card_le_globalHierarchyLoss
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne)
    (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (houter : s.restriction.outer = 1)
    (W : BohrData G) (H : SmoothingHierarchy W)
    (hWcard : W.carrier.card = C.childTwo.carrier.card) :
    ((endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card : ℝ) ≤
      ((twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W : ℕ) : ℝ) * (H.B₀.carrier.card : ℝ) := by
  have hendpoint :
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
        s.card :=
    endpointLocated_card_le_state_card s hmOne C hdense hepsilon_lt_one houter
  have hstate :
      s.card ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo * W.carrier.card := by
    have hC := C.cardTwo
    unfold DensityStep.LocatedRestriction.card BohrStopping.RegularRestriction.card
      BohrStopping.RegularRestriction.ambient
    rw [hWcard]
    simpa [houter] using hC
  have hhier := smoothingHierarchy_card_loss W H
  have hnat :
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
        (twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W) * H.B₀.carrier.card := by
    calc
      (endpointLocated s C.childOne C.childTwo hdense hepsilon_lt_one).card ≤
          s.card := hendpoint
      _ ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo * W.carrier.card := hstate
      _ ≤ twoReciprocalLoss s.restriction.bohr mOne mTwo *
          (smoothingHierarchyLoss W * H.B₀.carrier.card) :=
        Nat.mul_le_mul_left _ hhier
      _ = (twoReciprocalLoss s.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W) * H.B₀.carrier.card := by ring
  exact_mod_cast hnat

section EndpointHighNorm

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Rewrite the DRC sifted-density lower bound in the normalized
autocorrelation scale used by the high-norm branch.

The indicator correlation is |A|² times the probability correlation, while
the DRC denominator is |A|^(2p).  After taking the weighted p-norm, one
factor |A| remains.  This is the normalization identity that turns endpoint
density into a d-only lower bound for the later relative-T sample. -/
theorem siftingDensityLower_eq_normalizedLp
    (A B₁ B₂ : Finset G) {p : ℕ} (hp : 0 < p) :
    DensityStep.siftingDensityLower A B₁ B₂ p =
      (4 : ℝ)⁻¹ *
        ((A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) p) ^ (2 * p) := by
  let w : G → ℝ≥0 := μ B₁ ○ᵈ μ B₂
  have hcorr :
      (𝟭_[A, Real] ○ᵈ 𝟭_[A]) =
        ((A.card : ℝ) ^ 2) • (μ_[ℝ] A ○ᵈ μ A) := by
    rw [← card_smul_mu ℝ A, smul_dddconv, dddconv_smul]
    funext x
    simp [Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  have hscale :=
    LocalizedUnbalancing.weightedLpNorm_smul_of_nonneg w
      (μ_[ℝ] A ○ᵈ μ A) ((A.card : ℝ) ^ 2) (by positivity) hp
  have hnorm :
      ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] =
        (A.card : ℝ) ^ 2 *
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ w)
            (μ_[ℝ] A ○ᵈ μ A) p := by
    rw [hcorr]
    simpa only [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm w
      ((A.card : ℝ) ^ 2 • (μ_[ℝ] A ○ᵈ μ A)) hp] using hscale
  dsimp [w, Function.comp_def] at hnorm
  rw [DensityStep.siftingDensityLower, hnorm]
  by_cases hA0 : (A.card : ℝ) = 0
  · have htwo : 2 * p ≠ 0 := by omega
    simp [hA0, htwo]
  have hpow : (A.card : ℝ) ^ (2 * p) ≠ 0 := pow_ne_zero _ hA0
  field_simp [hpow]
  ring

/-- The DRC density lower bound is genuinely positive whenever the original
set and the two local base carriers meet.  This is the positivity input for
the relative-T Chang estimate; it is not obtained from the sifted output
inequalities, which are only upper bounds on the lower density. -/
theorem siftingDensityLower_pos_of_nonempty
    (A B₁ B₂ : Finset G) {p : ℕ} (hp : 0 < p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    0 < DensityStep.siftingDensityLower A B₁ B₂ p := by
  classical
  have hp0 : p ≠ 0 := hp.ne'
  have hB₁ : B₁.Nonempty := hB.mono Finset.inter_subset_left
  have hB₂ : B₂.Nonempty := hB.mono Finset.inter_subset_right
  let N : ℝ := ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]
  have hsumEq :=
    DensityStep.sum_card_siftedSet_mul_card_siftedSet A B₁ B₂ p hp0 hB₁ hB₂
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a, ha⟩ := hA
  let u₀ : Fin p → G := fun _ ↦ b - a
  have hA₁u₀ : b ∈ Sifting.siftedSet A B₁ u₀ := by
    simp only [Sifting.mem_siftedSet, u₀]
    refine ⟨Finset.inter_subset_left hb, ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hA₂u₀ : b ∈ Sifting.siftedSet A B₂ u₀ := by
    simp only [Sifting.mem_siftedSet, u₀]
    refine ⟨Finset.inter_subset_right hb, ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hsumPos :
      0 < ∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : ℝ) *
          (Sifting.siftedSet A B₂ u).card := by
    apply Finset.sum_pos'
    · intro u hu
      positivity
    · refine ⟨u₀, Finset.mem_univ _, ?_⟩
      exact mul_pos
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₁u₀⟩))
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₂u₀⟩))
  have hNp : 0 < N ^ p := by
    rw [hsumEq] at hsumPos
    have hcards : 0 < (B₁.card : ℝ) * B₂.card := by positivity
    rcases mul_pos_iff.mp hsumPos with hpos | hneg
    · simpa [N] using hpos.2
    · exact (not_lt_of_ge hcards.le hneg.1).elim
  have hNnonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hNne : N ≠ 0 := by
    intro hN0
    rw [hN0] at hNp
    simp [hp0] at hNp
  have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hNne)
  unfold DensityStep.siftingDensityLower
  have hAcard : (0 : ℝ) < A.card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨a, ha⟩)
  dsimp [N] at hNpos
  positivity

/-- In the large/small hierarchy orientation, the commuted LocalAP ratio
of A₁-cardinality to supported-popular cardinality is bounded below by half
of any lower bound for the common sifted density.  This is exactly the
logarithmic ratio consumed by RawSupplyNumerics. -/
theorem supported_ratio_lower_of_hierarchy
    (H : SmoothingHierarchy W)
    {A : Finset G} {p : ℕ} {sigma delta alpha : ℝ} (z : G)
    (data : DensityStep.SiftedPopularData A
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (halpha : 0 ≤ alpha)
    (halpha_le :
      alpha ≤ DensityStep.siftingDensityLower A
        (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p) :
    alpha / 2 ≤
      (data.A₁.card : ℝ) /
        (DensityStep.SiftedPopularData.supportedPopularSet A
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma).card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet A
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  have hSnonempty : S.Nonempty := by
    simpa [S] using data.supportedPopularSet_nonempty hdelta
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hSnonempty.card_pos
  have hBcard :
      ((z +ᵥ H.Dbohr.carrier).card : ℝ) =
        (H.Dbohr.carrier.card : ℝ) := by
    simp
  have hAone :
      alpha * (H.Dbohr.carrier.card : ℝ) ≤ (data.A₁.card : ℝ) := by
    have hdense :
        alpha ≤ (data.A₁.card : ℝ) / (z +ᵥ H.Dbohr.carrier).card :=
      halpha_le.trans data.density_one
    rw [hBcard] at hdense
    have hDpos : (0 : ℝ) < H.Dbohr.carrier.card := by
      exact_mod_cast H.Dbohr.carrier_nonempty.card_pos
    exact (le_div_iff₀ hDpos).mp hdense
  have hScardNat :
      S.card ≤ 2 * H.Dbohr.carrier.card := by
    calc
      S.card ≤ ((z +ᵥ H.Dbohr.carrier) - H.Ebohr.carrier).card := by
        exact Finset.card_le_card
          (DensityStep.SiftedPopularData.supportedPopularSet_subset_sub
            A (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma)
      _ ≤ 2 * H.Dbohr.carrier.card :=
        card_vadd_sub_small_le_two_mul_card H.Dbohr H.D_regular
          H.Ebohr.carrier H.E_in_Dtheta H.theta_small z
  have hScard : (S.card : ℝ) ≤ 2 * (H.Dbohr.carrier.card : ℝ) := by
    exact_mod_cast hScardNat
  apply (le_div_iff₀ hSpos).2
  calc
    alpha / 2 * (S.card : ℝ) ≤
        alpha / 2 * (2 * (H.Dbohr.carrier.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hScard (by positivity)
    _ = alpha * (H.Dbohr.carrier.card : ℝ) := by ring
    _ ≤ (data.A₁.card : ℝ) := hAone

/-- Turn the favorable A₁/S ratio into the square-root reciprocal bound
appearing in the commuted LocalAP error term. -/
theorem sqrt_supported_ratio_le_two_div
    {A₁ S : Finset G} {alpha : ℝ}
    (halpha : 0 < alpha) (hA₁ : A₁.Nonempty) (hS : S.Nonempty)
    (hratio : alpha / 2 ≤ (A₁.card : ℝ) / S.card) :
    Real.sqrt ((S.card : ℝ) / A₁.card) ≤ Real.sqrt (2 / alpha) := by
  have hA₁pos : (0 : ℝ) < A₁.card := by exact_mod_cast hA₁.card_pos
  have hSpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmul : alpha / 2 * (S.card : ℝ) ≤ (A₁.card : ℝ) :=
    (le_div_iff₀ hSpos).mp hratio
  have hdiv : (S.card : ℝ) / A₁.card ≤ 2 / alpha := by
    apply (div_le_div_iff₀ hA₁pos halpha).2
    nlinarith
  exact Real.sqrt_le_sqrt hdiv

/-- RawSupplyNumerics pays the phase and tail terms, while a single width
input pays the regular-Bohr translation term.  Together they give the fixed
1/512 commuted LocalAP error target. -/
theorem dyadic_commuted_hsmall
    (d : ℕ) {rank : ℕ} {kappa : NNReal}
    {A₁ S : Finset G}
    (hA₁ : A₁.Nonempty) (hS : S.Nonempty)
    (hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (A₁.card : ℝ) / S.card)
    (hwidth :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
        1 / 2048) :
    2 * RawSupplyNumerics.approximationDelta +
        (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ) +
          400 * ((max rank 1 : ℕ) : ℝ) *
            (kappa + kappa : NNReal) +
          2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤ (1 / 512 : ℝ) := by
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hsqrt :
      Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) :=
    sqrt_supported_ratio_le_two_div halphaPos hA₁ hS hratio
  have hphase :
      (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ)) *
          Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
            gcongr
      _ ≤ 1 / 2048 := RawSupplyNumerics.dyadic_quantized_phase_mul_sqrt_le d
  have hwidth' :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (400 * ((max rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
          gcongr
      _ ≤ 1 / 2048 := hwidth
  have htail :
      (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤ 1 / 2048 := by
    calc
      (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt ((S.card : ℝ) / A₁.card) ≤
        (2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
            gcongr
      _ ≤ 1 / 2048 := RawSupplyNumerics.dyadic_tail_error_mul_sqrt_le d
  unfold RawSupplyNumerics.approximationDelta
  nlinarith

/-- Natural denominator behind the deliberately tiny final LocalAP width. -/
def dyadicHierarchyDenominator (d rankCap : ℕ) : ℕ :=
  8388608 * max rankCap 1 *
    2 ^ (2 + 2 * d * RawSupplyNumerics.smoothingExponent d)

/-- A deliberately tiny reciprocal width for the final LocalAP child.
The factor 2^23 pays the regular-translation contribution after the crude
Real.sqrt(2/alpha) ≤ 2/alpha bound. -/
def dyadicHierarchyKappa (d rankCap : ℕ) : NNReal :=
  ((dyadicHierarchyDenominator d rankCap : ℕ) : NNReal)⁻¹

lemma dyadicHierarchyDenominator_pos (d rankCap : ℕ) :
    0 < dyadicHierarchyDenominator d rankCap := by
  unfold dyadicHierarchyDenominator
  positivity

lemma dyadicHierarchyKappa_width
    (d rankCap rank : ℕ) (hrank : rank ≤ rankCap) :
    (400 * ((max rank 1 : ℕ) : ℝ) *
        (dyadicHierarchyKappa d rankCap +
          dyadicHierarchyKappa d rankCap : NNReal)) *
      Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
      1 / 2048 := by
  let e : ℕ := 2 + 2 * d * RawSupplyNumerics.smoothingExponent d
  let P : ℕ := dyadicHierarchyDenominator d rankCap
  have hPpos : (0 : ℝ) < P := by
    dsimp [P, dyadicHierarchyDenominator, e]
    positivity
  have hmax : max rank 1 ≤ max rankCap 1 :=
    max_le_max_right 1 hrank
  have hsqrt :
      Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
        2 / RawSupplyNumerics.dyadicSiftedAlpha d :=
    RawSupplyNumerics.sqrt_two_div_le_two_div
      (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hbound :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (dyadicHierarchyKappa d rankCap +
            dyadicHierarchyKappa d rankCap : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (dyadicHierarchyKappa d rankCap +
            dyadicHierarchyKappa d rankCap : NNReal)) *
        (2 / RawSupplyNumerics.dyadicSiftedAlpha d) := by
    gcongr
  apply hbound.trans
  unfold dyadicHierarchyKappa dyadicHierarchyDenominator
    RawSupplyNumerics.dyadicSiftedAlpha
  change
    (400 * ((max rank 1 : ℕ) : ℝ) *
        (((P : ℕ) : ℝ)⁻¹ + ((P : ℕ) : ℝ)⁻¹)) *
      (2 / (1 / (2 : ℝ) ^ e)) ≤ 1 / 2048
  have hmaxReal : ((max rank 1 : ℕ) : ℝ) ≤ max rankCap 1 := by
    exact_mod_cast hmax
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hcalc :
      (400 * ((max rank 1 : ℕ) : ℝ) *
          (((P : ℕ) : ℝ)⁻¹ + ((P : ℕ) : ℝ)⁻¹)) *
        (2 / (1 / (2 : ℝ) ^ e)) =
      1600 * ((max rank 1 : ℕ) : ℝ) * (2 : ℝ) ^ e / P := by
    field_simp
    ring
  rw [hcalc]
  have hP :
      (8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e =
        (P : ℝ) := by
    dsimp [P, dyadicHierarchyDenominator]
    norm_cast
  rw [← hP]
  have hden : (0 : ℝ) <
      (8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e := by
    positivity
  apply (div_le_iff₀ hden).2
  calc
    1600 * ((max rank 1 : ℕ) : ℝ) * (2 : ℝ) ^ e ≤
        1600 * ((max rankCap 1 : ℕ) : ℝ) * (2 : ℝ) ^ e := by
      gcongr
    _ ≤ (1 / 2048 : ℝ) *
        ((8388608 : ℝ) * (max rankCap 1 : ℕ) * (2 : ℝ) ^ e) := by
      have hmaxPos : (0 : ℝ) < (max rankCap 1 : ℕ) := by positivity
      nlinarith

lemma two_dyadicHierarchyKappa_le_rank_scale
    (d rankCap rank : ℕ) (hrank : rank ≤ rankCap) :
    dyadicHierarchyKappa d rankCap + dyadicHierarchyKappa d rankCap ≤
      1 / (100 * (max rank 1 : ℕ) : NNReal) := by
  let e : ℕ := 2 + 2 * d * RawSupplyNumerics.smoothingExponent d
  let P : ℕ := dyadicHierarchyDenominator d rankCap
  have hPpos : (0 : ℝ) < P := by
    dsimp [P, dyadicHierarchyDenominator, e]
    positivity
  have hrpos : (0 : ℝ) < 100 * (max rank 1 : ℕ) := by positivity
  have hmax : max rank 1 ≤ max rankCap 1 :=
    max_le_max_right 1 hrank
  have hnat : 2 * (100 * max rank 1) ≤ P := by
    dsimp [P, dyadicHierarchyDenominator]
    have hpow : 1 ≤ 2 ^ e := Nat.one_le_pow _ _ (by omega)
    calc
      2 * (100 * max rank 1) ≤ 200 * max rankCap 1 := by
        omega
      _ ≤ 8388608 * max rankCap 1 * 2 ^ e := by
        have hcoeff : 200 ≤ 8388608 := by norm_num
        calc
          200 * max rankCap 1 ≤ 8388608 * max rankCap 1 :=
            Nat.mul_le_mul_right _ hcoeff
          _ ≤ 8388608 * max rankCap 1 * 2 ^ e :=
            Nat.le_mul_of_pos_right _ (by positivity)
  have hreal :
      (2 : ℝ) * (P : ℝ)⁻¹ ≤
        1 / (100 * (max rank 1 : ℕ) : ℝ) := by
    have hnatReal : (2 : ℝ) * (100 * (max rank 1 : ℕ)) ≤ P := by
      exact_mod_cast hnat
    field_simp
    linarith
  unfold dyadicHierarchyKappa
  change
    ((P : ℕ) : NNReal)⁻¹ + ((P : ℕ) : NNReal)⁻¹ ≤
      1 / (100 * (max rank 1 : ℕ) : NNReal)
  have hnn :
      (2 : NNReal) * ((P : ℕ) : NNReal)⁻¹ ≤
        1 / (100 * (max rank 1 : ℕ) : NNReal) := by
    exact_mod_cast hreal
  simpa [two_mul] using hnn

/-- A dyadic lower bound for the common sifted density and the canonical
sample-count upper bound imply the fixed dyadic Chang-rank budget. -/
theorem hierarchy_rankBudget_of_dyadic_lower
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d) :
    ⌈8 * (1 + Real.log (2 /
      hierarchyBeta W H data k))⌉₊ ≤
      RawSupplyNumerics.dyadicRankCost d := by
  let alpha := RawSupplyNumerics.dyadicSiftedAlpha d
  let K := RawSupplyNumerics.dyadicSampleKBound d
  let sift := DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p
  have halphaPos : 0 < alpha := by
    simpa [alpha] using RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have halphaOne : alpha ≤ 1 := by
    simpa [alpha] using RawSupplyNumerics.dyadicSiftedAlpha_le_one d
  have hsiftPos : 0 < sift := halphaPos.trans_le (by simpa [sift, alpha] using halpha_le)
  have hbaseNonneg : 0 ≤ alpha / 2 := by positivity
  have hbaseOne : alpha / 2 ≤ 1 := by linarith
  have hpowExp : (alpha / 2) ^ K ≤ (alpha / 2) ^ k := by
    have hK : k + (K - k) = K := Nat.add_sub_of_le hk
    calc
      (alpha / 2) ^ K = (alpha / 2) ^ (k + (K - k)) := by rw [hK]
      _ = (alpha / 2) ^ k * (alpha / 2) ^ (K - k) := by rw [pow_add]
      _ ≤ (alpha / 2) ^ k * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ hbaseNonneg hbaseOne) (by positivity)
      _ = (alpha / 2) ^ k := by ring
  have hpowBase : (alpha / 2) ^ k ≤ (sift / 2) ^ k := by
    apply pow_le_pow_left₀
    · positivity
    · simpa [sift, alpha] using (div_le_div_of_nonneg_right halpha_le (by norm_num))
  have hbetaLower :
      RawSupplyNumerics.crootBeta alpha K ≤ hierarchyBeta W H data k := by
    unfold RawSupplyNumerics.crootBeta hierarchyBeta
    exact div_le_div_of_nonneg_right (hpowExp.trans hpowBase) (by norm_num)
  have hbetaPos : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hcrootPos : 0 < RawSupplyNumerics.crootBeta alpha K :=
    RawSupplyNumerics.crootBeta_pos halphaPos
  have hdiv :
      2 / hierarchyBeta W H data k ≤
        2 / RawSupplyNumerics.crootBeta alpha K := by
    exact div_le_div_of_nonneg_left (by norm_num) hcrootPos hbetaLower
  have hlog :
      Real.log (2 / hierarchyBeta W H data k) ≤
        Real.log (2 / RawSupplyNumerics.crootBeta alpha K) :=
    Real.log_le_log (by positivity) hdiv
  have hinside :
      8 * (1 + Real.log (2 / hierarchyBeta W H data k)) ≤
        8 * (1 + Real.log (2 / RawSupplyNumerics.crootBeta alpha K)) := by
    nlinarith
  apply le_trans (Nat.ceil_mono hinside)
  unfold RawSupplyNumerics.dyadicRankCost RawSupplyNumerics.changRankCost
  exact le_max_right _ _

/-- The real Chang dimension obeys the same dyadic budget.  This is the
version needed to bound the spectral quantization factor in the localized
cell count. -/
theorem hierarchy_dimension_le_dyadicRankCost
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) ≤
      RawSupplyNumerics.dyadicRankCost d := by
  have hsiftPos :
      0 < DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p :=
    (RawSupplyNumerics.dyadicSiftedAlpha_pos d).trans_le halpha_le
  have hbeta : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hdim := hierarchy_dimension_le_of_croot W H data hdelta k T hbeta hT
  have hceil :
      8 * (1 + Real.log (2 / hierarchyBeta W H data k)) ≤
        (⌈8 * (1 + Real.log (2 / hierarchyBeta W H data k))⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hrank := hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  have hrankReal :
      (⌈8 * (1 + Real.log (2 / hierarchyBeta W H data k))⌉₊ : ℝ) ≤
        RawSupplyNumerics.dyadicRankCost d := by
    exact_mod_cast hrank
  exact hdim.trans (hceil.trans hrankReal)

/-- A single fixed cell multiplier dominates every commuted relative-T
package at the dyadic scale once the parent rank is capped. -/
theorem hierarchy_cellMultiplier_le_dyadic
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k rankCap : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (hB₀rank : H.B₀.rank ≤ rankCap)
    (T : Finset G) (Delta : Finset (AddChar G Complex))
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)))
    (hDelta : (Delta.card : ℝ) ≤
      RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)) :
    (RawSupplyNumerics.dyadicQQuant d *
        LocalizedAlmostPeriodicity.spectralQuantization
          (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
        Delta.card * 4 ^ (H.B₀.rank + Delta.card) ≤
      RawSupplyNumerics.cellMultiplier rankCap
        (RawSupplyNumerics.dyadicRankCost d)
        (RawSupplyNumerics.dyadicQQuant d *
          (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1)) := by
  let dim := RelativeChangSanders.localChangDimension H.B₀ T (1 / 2)
  have hdim : dim ≤ RawSupplyNumerics.dyadicRankCost d := by
    simpa [dim] using hierarchy_dimension_le_dyadicRankCost W H data hdelta d k
      halpha_le hk T hT
  have hspectral :
      LocalizedAlmostPeriodicity.spectralQuantization dim ≤
        ⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1 := by
    unfold LocalizedAlmostPeriodicity.spectralQuantization
    apply Nat.add_le_add_right
    apply Nat.ceil_mono
    have hmax : max dim 0 ≤ (RawSupplyNumerics.dyadicRankCost d : ℝ) :=
      max_le hdim (by positivity)
    have hpi : 2 * Real.pi ≤ (8 : ℝ) := by
      nlinarith [Real.pi_lt_four]
    calc
      2 * Real.pi * max dim 0 ≤
          2 * Real.pi * RawSupplyNumerics.dyadicRankCost d := by
        gcongr
      _ ≤ 8 * (RawSupplyNumerics.dyadicRankCost d : ℝ) := by
        gcongr
  have hq : 0 < RawSupplyNumerics.dyadicQQuant d := by
    unfold RawSupplyNumerics.dyadicQQuant
    exact RawSupplyNumerics.qQuant_pos (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
  have hspecPos :
      0 < LocalizedAlmostPeriodicity.spectralQuantization dim := by
    unfold LocalizedAlmostPeriodicity.spectralQuantization
    positivity
  have hn :
      0 < RawSupplyNumerics.dyadicQQuant d *
        LocalizedAlmostPeriodicity.spectralQuantization dim :=
    Nat.mul_pos hq hspecPos
  have hnN :
      RawSupplyNumerics.dyadicQQuant d *
          LocalizedAlmostPeriodicity.spectralQuantization dim ≤
        RawSupplyNumerics.dyadicQQuant d *
          (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1) :=
    Nat.mul_le_mul_left _ hspectral
  have hsiftPos :
      0 < DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p :=
    (RawSupplyNumerics.dyadicSiftedAlpha_pos d).trans_le halpha_le
  have hbeta : 0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hdeltaCard : Delta.card ≤ RawSupplyNumerics.dyadicRankCost d := by
    apply (hierarchy_delta_card_le_of_croot W H data hdelta k T Delta
      hbeta hT hDelta).trans
    exact hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  simpa [RawSupplyNumerics.cellMultiplier, dim] using
    RawSupplyNumerics.cellMultiplier_mono hn hnN hB₀rank hdeltaCard

/-- The high local norm threshold forces the exact dyadic lower bound for
the common sifted density.  The harmless factor 65/64 is intentionally
larger than one, so the endpoint density alone pays the dyadic power. -/
theorem dyadicSiftedAlpha_le_siftingDensity_of_localNorm
    (A B₁ B₂ K : Finset G) (d : ℕ)
    (hK : K.Nonempty)
    (hdensity : 1 / (2 : ℝ) ^ d ≤ (A.card : ℝ) / K.card)
    (hnorm :
      (65 / 64 : ℝ) * (K.card : ℝ)⁻¹ ≤
        BalancedRestriction.weightedLpNorm
          (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
          (μ_[ℝ] A ○ᵈ μ A)
          (RawSupplyNumerics.smoothingExponent d)) :
    RawSupplyNumerics.dyadicSiftedAlpha d ≤
      DensityStep.siftingDensityLower A B₁ B₂
        (RawSupplyNumerics.smoothingExponent d) := by
  let r := RawSupplyNumerics.smoothingExponent d
  have hr : 0 < r := by
    simpa [r] using RawSupplyNumerics.smoothingExponent_pos d
  have hKpos : (0 : ℝ) < K.card := by exact_mod_cast hK.card_pos
  have hAcardNonneg : (0 : ℝ) ≤ A.card := by positivity
  have hratioNonneg : 0 ≤ (A.card : ℝ) / K.card := by positivity
  have hproduct :
      1 / (2 : ℝ) ^ d ≤
        (A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) r := by
    calc
      1 / (2 : ℝ) ^ d ≤ (A.card : ℝ) / K.card := hdensity
      _ ≤ (65 / 64 : ℝ) * ((A.card : ℝ) / K.card) := by
        nlinarith
      _ = (A.card : ℝ) * ((65 / 64 : ℝ) * (K.card : ℝ)⁻¹) := by
        field_simp
      _ ≤ (A.card : ℝ) *
          BalancedRestriction.weightedLpNorm
            (fun x : G => ((μ_[ℝ≥0] B₁ ○ᵈ μ B₂) x : ℝ))
            (μ_[ℝ] A ○ᵈ μ A) r :=
        mul_le_mul_of_nonneg_left (by simpa [r] using hnorm) hAcardNonneg
  have hrewrite :
      RawSupplyNumerics.dyadicSiftedAlpha d =
        (4 : ℝ)⁻¹ * (1 / (2 : ℝ) ^ d) ^ (2 * r) := by
    unfold RawSupplyNumerics.dyadicSiftedAlpha
    unfold RawSupplyNumerics.dyadicAlphaExponent
    dsimp [r]
    simp only [one_div, ← inv_pow, pow_add, pow_mul]
    field_simp
    have hpow :
        (1 / 2 : ℝ) ^
            (d * RawSupplyNumerics.smoothingExponent d * 2) *
          (4 : ℝ) ^ (d * RawSupplyNumerics.smoothingExponent d) = 1 := by
      rw [show d * RawSupplyNumerics.smoothingExponent d * 2 =
          2 * (d * RawSupplyNumerics.smoothingExponent d) by omega]
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]
      rw [one_div, inv_pow]
      field_simp
    norm_num [pow_mul, pow_add] at hpow ⊢
    have hcomm :
        (((1 / 2 : ℝ) ^ d) ^ RawSupplyNumerics.smoothingExponent d) ^ 2 =
          (((1 / 2 : ℝ) ^ d) ^ 2) ^
            RawSupplyNumerics.smoothingExponent d := by
      conv_lhs =>
        rw [← pow_mul, ← pow_mul]
      conv_rhs =>
        rw [← pow_mul, ← pow_mul]
      congr 1
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hcomm] at hpow
    nlinarith
  rw [hrewrite, siftingDensityLower_eq_normalizedLp A B₁ B₂ hr]
  gcongr

/-- The fixed high-norm parameters satisfy the Croot--Sisask tail
condition at every dyadic scale. -/
theorem dyadic_smoothing_tail_bound (d : ℕ) :
    ((1 / 8192 : ℝ)⁻¹) * Real.log (2 / (1 / 8192 : ℝ)) ≤
      RawSupplyNumerics.smoothingExponent d := by
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num) using 1
    norm_num
  have hlog : Real.log (2 / (1 / 8192 : ℝ)) ≤ 14 := by
    rw [show (2 / (1 / 8192 : ℝ)) = (2 : ℝ) ^ 14 by norm_num,
      Real.log_pow]
    norm_num at hlog2 ⊢
    nlinarith
  have hleft :
      ((1 / 8192 : ℝ)⁻¹) * Real.log (2 / (1 / 8192 : ℝ)) ≤
        (114688 : ℝ) := by
    norm_num
    nlinarith
  apply hleft.trans
  unfold RawSupplyNumerics.smoothingExponent RawSupplyNumerics.holderExponent
  rw [BalancedRestriction.stoppingExponent_eq]
  norm_num [unbalancingMultiplier]
  have hd : 1 ≤ d + 1 := by omega
  norm_num at hd ⊢
  nlinarith

/-- The deliberately slack high threshold leaves room for the fixed
popular-set, DRC, and localized-approximation errors. -/
theorem dyadic_high_gain_numeric :
    (1 + (1 / 8 : ℝ) / 32) ≤
      (65 / 64 : ℝ) * (1 - 1 / 8192) *
        (1 - 1 / 8192 - 1 / 512) := by
  norm_num

/-- At the endpoint fibre, the fixed high threshold and the three fixed
errors give the 257/256 density gain required by the rank-regular high
branch. -/
theorem endpoint_dyadic_high_gain
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense_lt_one : epsilonDense < 1) :
    (1 + (1 / 8 : ℝ) / 32) *
        (endpointLocated s C.childOne C.childTwo hdense
          hepsilonDense_lt_one).density ≤
      ((endpointLocated s C.childOne C.childTwo hdense
          hepsilonDense_lt_one).restriction.set.card : ℝ) *
        (((1 - (1 / 8192 : ℝ)) *
            ((65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹)) *
          (1 - (1 / 8192 : ℝ) - (1 / 512 : ℝ))) := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  have hKpos : (0 : ℝ) < C.childOne.bohr.carrier.card := by
    exact_mod_cast C.childOne.bohr.carrier_nonempty.card_pos
  have hdensity :
      u.density = (u.restriction.set.card : ℝ) /
        C.childOne.bohr.carrier.card := by
    simp only [u, endpointLocated, DensityStep.density_narrowLocated]
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      C.childOne.carrier_nonempty]
    simp [DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
      C.childOne_carrier]
  rw [show (endpointLocated s C.childOne C.childTwo hdense
      hepsilonDense_lt_one).density = u.density by rfl,
    show (endpointLocated s C.childOne C.childTwo hdense
      hepsilonDense_lt_one).restriction.set = u.restriction.set by rfl,
    hdensity]
  have hnum := dyadic_high_gain_numeric
  have hA : (0 : ℝ) ≤ u.restriction.set.card := by positivity
  calc
    (1 + (1 / 8 : ℝ) / 32) *
        ((u.restriction.set.card : ℝ) / C.childOne.bohr.carrier.card) ≤
      ((65 / 64 : ℝ) * (1 - 1 / 8192) *
        (1 - 1 / 8192 - 1 / 512)) *
          ((u.restriction.set.card : ℝ) / C.childOne.bohr.carrier.card) := by
      gcongr
    _ = (u.restriction.set.card : ℝ) *
        (((1 - (1 / 8192 : ℝ)) *
            ((65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹)) *
          (1 - (1 / 8192 : ℝ) - (1 / 512 : ℝ))) := by
      field_simp

/-- One extra dyadic bit pays for the 511/512 dense-pair loss before the
high branch is run on the endpoint fibre. -/
theorem endpointLocated_on_nextDyadicScale
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense : epsilonDense = (1 / 512 : ℝ))
    (hepsilonDense_lt_one : epsilonDense < 1)
    {d : ℕ} (hscale : 1 / (2 : ℝ) ^ d ≤ s.density) :
    1 / (2 : ℝ) ^ (d + 1) ≤
      (endpointLocated s C.childOne C.childTwo hdense
        hepsilonDense_lt_one).density := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  have huDensity : densePairDensity s epsilonDense ≤ u.density := by
    let x := GroupCount.densePairPoint hdense
    have hx : densePairDensity s epsilonDense ≤
        localDensity s.restriction.set C.childOne.carrier x := by
      simpa [x, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    simpa [u, endpointLocated, DensityStep.density_narrowLocated] using hx
  have hhalf :
      1 / (2 : ℝ) ^ (d + 1) ≤
        (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d) := by
    rw [pow_succ]
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ d := by positivity
    field_simp
    nlinarith
  calc
    1 / (2 : ℝ) ^ (d + 1) ≤
        (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d) := hhalf
    _ ≤ (1 - (1 / 512 : ℝ)) * s.density := by gcongr
    _ = densePairDensity s epsilonDense := by simp [densePairDensity, hepsilonDense]
    _ ≤ u.density := huDensity

/-- The larger Holder exponent at d+1 still satisfies the dense-pair power
condition required by the raw endpoint. -/
theorem densePairDensity_power_next_of_dyadic
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d : ℕ} (hscale : 1 / (2 : ℝ) ^ d ≤ s.density) :
    (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent (d + 1) ≤
      densePairDensity s (1 / 512 : ℝ) := by
  have hbase : 0 ≤ (2 / 3 : ℝ) := by norm_num
  have hbaseOne : (2 / 3 : ℝ) ≤ 1 := by norm_num
  have hexp : RawSupplyNumerics.holderExponent d ≤
      RawSupplyNumerics.holderExponent (d + 1) := by
    unfold RawSupplyNumerics.holderExponent
    omega
  calc
    (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent (d + 1) ≤
        (2 / 3 : ℝ) ^ RawSupplyNumerics.holderExponent d := by
      exact pow_le_pow_of_le_one hbase hbaseOne hexp
    _ ≤ (1 - (1 / 512 : ℝ)) * s.density := by
      simpa [RawSupplyNumerics.holderExponent] using
        densePairDensity_power_of_dyadic s hscale
    _ = densePairDensity s (1 / 512 : ℝ) := by
      simp [densePairDensity]

/-- A convenient abstract boundary-width calculation: if the endpoint has
density at least alpha in the base carrier and the regularity width is at
most alpha/384, then the Holder boundary error is below 1/64 of the base
scale. -/
theorem boundary_width_of_endpoint_density
    {Acard Kcard alpha width : ℝ}
    (hAcard : 0 < Acard) (hKcard : 0 < Kcard)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hAK : alpha * Kcard ≤ Acard)
    (hwidth : width ≤ alpha / 384) (hwidthNonneg : 0 ≤ width) :
    2 * (Acard⁻¹ * width) + Kcard⁻¹ * width ≤
      (1 / 64 : ℝ) * Kcard⁻¹ := by
  have hAlphaK : 0 < alpha * Kcard := mul_pos halpha hKcard
  have hAinv : Acard⁻¹ ≤ (alpha * Kcard)⁻¹ :=
    (inv_le_inv₀ hAcard hAlphaK).2 hAK
  have hfirst : Acard⁻¹ * width ≤ Kcard⁻¹ / 384 := by
    calc
      Acard⁻¹ * width ≤ (alpha * Kcard)⁻¹ * width := by gcongr
      _ ≤ (alpha * Kcard)⁻¹ * (alpha / 384) := by gcongr
      _ = Kcard⁻¹ / 384 := by
        field_simp
  have hwidthOne : width ≤ 1 / 384 := by
    calc
      width ≤ alpha / 384 := hwidth
      _ ≤ 1 / 384 := by gcongr
  have hsecond : Kcard⁻¹ * width ≤ Kcard⁻¹ / 384 := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hwidthOne (by positivity : 0 ≤ Kcard⁻¹)
  calc
    2 * (Acard⁻¹ * width) + Kcard⁻¹ * width ≤
        2 * (Kcard⁻¹ / 384) + Kcard⁻¹ / 384 := by gcongr
    _ ≤ (1 / 64 : ℝ) * Kcard⁻¹ := by
      have hKinv : 0 ≤ Kcard⁻¹ := by positivity
      nlinarith

/-- The concrete second reciprocal denominator makes the Holder boundary
width small enough on a dyadic-density endpoint fibre. -/
theorem dyadic_boundary_width
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {d rankCost mOne : ℕ}
    (C : ReciprocalChildren s.restriction.bohr mOne
      (ConcreteNumerics.mTwo (d + 1) rankCost))
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo (1 / 512 : ℝ))
    (hscale : 1 / (2 : ℝ) ^ d ≤ s.density)
    (hrank : s.rank ≤ ConcreteNumerics.rankCap (d + 1) rankCost)
    (hrankCost : 0 < rankCost) :
    2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
        (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
          (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
            (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ))) +
      (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
        (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
          (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
            (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
  let alpha : ℝ := (1 - (1 / 512 : ℝ)) * (1 / (2 : ℝ) ^ d)
  let width : ℝ :=
    200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
      (((ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ +
        (ConcreteNumerics.mTwo (d + 1) rankCost : NNReal)⁻¹ : NNReal) : ℝ)
  have hAne : (endpointSet s C.childOne C.childTwo hdense).Nonempty :=
    endpointSet_nonempty s C.childOne C.childTwo hdense (by norm_num)
  have hApos : (0 : ℝ) < (endpointSet s C.childOne C.childTwo hdense).card := by
    exact_mod_cast hAne.card_pos
  have hKpos : (0 : ℝ) < C.childOne.bohr.carrier.card := by
    exact_mod_cast C.childOne.bohr.carrier_nonempty.card_pos
  have halphaPos : 0 < alpha := by unfold alpha; positivity
  have halphaOne : alpha ≤ 1 := by
    unfold alpha
    have hdensity : 1 / (2 : ℝ) ^ d ≤ 1 := by
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
      exact (div_le_iff₀ (by positivity)).2 (by simpa using hpow)
    nlinarith
  have hOne : alpha ≤
      localDensity s.restriction.set C.childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    calc
      alpha ≤ (1 - (1 / 512 : ℝ)) * s.density := by
        unfold alpha
        gcongr
      _ = densePairDensity s (1 / 512 : ℝ) := by simp [densePairDensity]
      _ ≤ localDensity s.restriction.set C.childOne.carrier
          (GroupCount.densePairPoint hdense) := by
        simpa [densePairDensity] using GroupCount.densePairPoint_density_one hdense
  have hAK : alpha * (C.childOne.bohr.carrier.card : ℝ) ≤
      (endpointSet s C.childOne C.childTwo hdense).card := by
    rw [DensityStep.localDensity_eq_card_narrowingSet_div
      C.childOne.carrier_nonempty] at hOne
    have hCpos : (0 : ℝ) < C.childOne.carrier.card := by
      exact_mod_cast C.childOne.carrier_nonempty.card_pos
    simpa [endpointSet, C.childOne_carrier] using
      (le_div_iff₀ hCpos).mp hOne
  have hwidthNonneg : 0 ≤ width := by unfold width; positivity
  have hwidth : width ≤ alpha / 384 := by
    have hmax : max C.childOne.bohr.rank 1 ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by
      rw [C.rankOne]
      exact ConcreteNumerics.max_rank_le_rankCap hrankCost hrank
    have hmPos : (0 : ℝ) < ConcreteNumerics.mTwo (d + 1) rankCost := by
      exact_mod_cast ConcreteNumerics.mTwo_pos hrankCost
    have hRpos : (0 : ℝ) < ConcreteNumerics.rankCap (d + 1) rankCost := by
      exact_mod_cast ConcreteNumerics.rankCap_pos hrankCost
    have hmaxR : ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by exact_mod_cast hmax
    have hmaxR' : max (C.childOne.bohr.rank : ℝ) 1 ≤
        ConcreteNumerics.rankCap (d + 1) rankCost := by
      simpa [Nat.cast_max] using hmaxR
    unfold width alpha ConcreteNumerics.mTwo
    simp only [NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast]
    push_cast
    change 200 * max (C.childOne.bohr.rank : ℝ) 1 *
        ((76800 * ConcreteNumerics.rankCap (d + 1) rankCost *
          2 ^ (d + 1 + 1) : ℝ)⁻¹ +
          (76800 * ConcreteNumerics.rankCap (d + 1) rankCost *
          2 ^ (d + 1 + 1) : ℝ)⁻¹) ≤
      ((1 - 1 / 512) * (1 / (2 : ℝ) ^ d)) / 384
    field_simp
    have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
    have hpow2 : (2 : ℝ) ^ (d + 1 + 1) = 4 * (2 : ℝ) ^ d := by
      rw [show d + 1 + 1 = d + 2 by omega, pow_add]
      norm_num
      ring
    rw [hpow2]
    nlinarith
  convert boundary_width_of_endpoint_density hApos hKpos halphaPos halphaOne
      hAK hwidth hwidthNonneg using 1 <;> simp [width] <;> norm_num

/-- Consume the commuted, support-restricted relative-T constructor inside
the three-level smoothing hierarchy.

The hypotheses after hsmall are deliberately scalar bookkeeping obligations:
a uniform Chang-rank cap, a uniform multiplier cap, and the lower bound on
the regularized source carrier which pays that multiplier.  No
density-increment conclusion is assumed here. -/
theorem supportedLocalizedPackage_of_hierarchy
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set B₁
      H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : (B₁ ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (approxDelta : ℝ) (happroxDelta : 0 < approxDelta)
    (m : ℕ) (hm : m ≠ 0)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max H.B₀.rank 1 : ℕ) : NNReal))
    (qQuant : ℕ) (hqQuant : 0 < qQuant)
    (approximationError sizeCost : ℝ)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : ℝ) +
            400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : ℝ) ^ m) *
          Real.sqrt
            (((DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma).card : ℝ) /
              data.A₁.card) ≤ approximationError)
    {rankCost cardMultiplier : ℕ}
    (hB₀rank : H.B₀.rank ≤ s.rank)
    (hrankBudget :
      ⌈8 * (1 + Real.log (2 /
        hierarchyBeta W H data
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m)))⌉₊ ≤ rankCost)
    (hmult : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma))
              data.A₁ approxDelta m) ≤ (T.card : ℝ)) →
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      (qQuant * LocalizedAlmostPeriodicity.spectralQuantization
          (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
          Delta.card *
        4 ^ (H.B₀.rank + Delta.card) ≤ cardMultiplier)
    (hcardMultiplier : 0 < cardMultiplier)
    (hsource : ∀ (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
        (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set B₁ H.Ebohr.carrier p sigma))
            data.A₁ approxDelta m) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set B₁ H.Ebohr.carrier p sigma))
              data.A₁ approxDelta m) ≤ (T.card : ℝ)) →
      1 / 2 ≤ rho →
      C₀ = H.B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)) →
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ)) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source rankCost multiplier approximationError,
        P.child.rank ≤ s.rank + rankCost ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  obtain ⟨T, X, rho, C₀, Delta, hTcard, hTB₀, hXne, hDelta,
      hrhoHalf, hrhoOne, hC₀, Praw⟩ :=
    DensityStep.exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses_commuted
      data hdelta approxDelta happroxDelta m hm H.B₀ H.B₀_regular
      kappa hkappa qQuant hqQuant approximationError hsmall
  obtain ⟨Praw⟩ := Praw
  let rawMultiplier : ℕ :=
    (qQuant * LocalizedAlmostPeriodicity.spectralQuantization
        (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
        Delta.card *
      4 ^ (H.B₀.rank + Delta.card)
  let k : ℕ :=
    DensityStep.localizedAPSampleK
      (-(DensityStep.SiftedPopularData.supportedPopularSet
        s.restriction.set B₁ H.Ebohr.carrier p sigma))
      data.A₁ approxDelta m
  have hTcard' :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ)) := by
    simpa [k, hierarchyNegCard, hierarchySampleCard,
      hierarchyCrootCard, hierarchyCrootSumset] using hTcard
  have hsiftPos :
      0 < DensityStep.siftingDensityLower s.restriction.set B₁
        H.Ebohr.carrier p :=
    siftingDensityLower_pos_of_nonempty s.restriction.set B₁
      H.Ebohr.carrier hp hB s.restriction.nonempty
  have hbeta :
      0 < hierarchyBeta W H data k := by
    unfold hierarchyBeta
    positivity
  have hrank' : Delta.card ≤ rankCost := by
    apply (hierarchy_delta_card_le_of_croot W H data hdelta k T Delta
      hbeta hTcard' hDelta).trans
    simpa [k] using hrankBudget
  have hmult' : rawMultiplier ≤ cardMultiplier := by
    simpa [rawMultiplier] using hmult T Delta hTcard' hDelta
  let P := Praw.mono hrank' hmult' (le_refl approximationError)
  have hPrank : P.child.rank ≤ s.rank + rankCost := by
    have hraw := P.rank_bound
    calc
      P.child.rank ≤ H.B₀.rank + rankCost := by
        simpa [P, hC₀, BohrData.rank_dilate] using hraw
      _ ≤ s.rank + rankCost := Nat.add_le_add_right hB₀rank rankCost
  have hsource' :
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ) :=
    hsource T rho C₀ Delta hTcard' hrhoHalf hC₀
  have hrelative :
      ((C₀.dilate kappa).carrier.card : ℝ) ≤
        (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := by
    have hnat :
        (C₀.dilate kappa).carrier.card ≤
          cardMultiplier * P.child.carrier.card := by
      exact P.relative_card
    exact_mod_cast hnat
  have hmultCard :
      (cardMultiplier : ℝ) *
          (Real.exp (-sizeCost) * (s.card : ℝ)) ≤
        (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := by
    calc
      (cardMultiplier : ℝ) *
          (Real.exp (-sizeCost) * (s.card : ℝ)) =
          Real.exp (-sizeCost) * (s.card : ℝ) * cardMultiplier := by ring
      _ ≤ ((C₀.dilate kappa).carrier.card : ℝ) := hsource'
      _ ≤ (cardMultiplier : ℝ) * (P.child.carrier.card : ℝ) := hrelative
  have hmultPos : (0 : ℝ) < cardMultiplier := by exact_mod_cast hcardMultiplier
  have hPcard :
      Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card :=
    le_of_mul_le_mul_left hmultCard hmultPos
  exact ⟨C₀, kappa + kappa, (C₀.dilate kappa).carrier,
    cardMultiplier, P, hPrank, hPcard⟩

/-- Dyadic specialization of the local hierarchy adapter.  RawSupplyNumerics
now supplies both the sample-count and Chang-rank bounds; only the phase
error and pure volume/card-multiplier estimates remain as explicit scalar
inputs. -/
theorem supportedLocalizedPackage_of_dyadic_hierarchy
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {d : ℕ} (z : G)
    {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower s.restriction.set
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max H.B₀.rank 1 : ℕ) : NNReal))
    (approximationError sizeCost : ℝ)
    (happroximationError : (1 / 512 : ℝ) ≤ approximationError)
    (hwidth :
      (400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
          (kappa + kappa : NNReal)) *
        Real.sqrt (2 / RawSupplyNumerics.dyadicSiftedAlpha d) ≤
          1 / 2048)
    {cardMultiplier : ℕ}
    (hB₀rank : H.B₀.rank ≤ s.rank)
    (hmult : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma))
            data.A₁ RawSupplyNumerics.approximationDelta
              (RawSupplyNumerics.dyadicTailExponent d)) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                  H.Ebohr.carrier p sigma))
              data.A₁ RawSupplyNumerics.approximationDelta
                (RawSupplyNumerics.dyadicTailExponent d)) ≤ (T.card : ℝ)) →
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      (RawSupplyNumerics.dyadicQQuant d *
          LocalizedAlmostPeriodicity.spectralQuantization
            (RelativeChangSanders.localChangDimension H.B₀ T (1 / 2))) ^
          Delta.card *
        4 ^ (H.B₀.rank + Delta.card) ≤ cardMultiplier)
    (hcardMultiplier : 0 < cardMultiplier)
    (hsource : ∀ (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
        (Delta : Finset (AddChar G Complex)),
      ((hierarchyNegCard data.A₂ ^
          (DensityStep.localizedAPSampleK
            (-(DensityStep.SiftedPopularData.supportedPopularSet
              s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma))
            data.A₁ RawSupplyNumerics.approximationDelta
              (RawSupplyNumerics.dyadicTailExponent d)) / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^
            (DensityStep.localizedAPSampleK
              (-(DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                  H.Ebohr.carrier p sigma))
              data.A₁ RawSupplyNumerics.approximationDelta
                (RawSupplyNumerics.dyadicTailExponent d)) ≤ (T.card : ℝ)) →
      1 / 2 ≤ rho →
      C₀ = H.B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)) →
      Real.exp (-sizeCost) * (s.card : ℝ) * (cardMultiplier : ℝ) ≤
        ((C₀.dilate kappa).carrier.card : ℝ)) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source (RawSupplyNumerics.dyadicRankCost d)
          multiplier approximationError,
        P.child.rank ≤ s.rank + RawSupplyNumerics.dyadicRankCost d ∧
        Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  let k : ℕ :=
    DensityStep.localizedAPSampleK (-S) data.A₁
      RawSupplyNumerics.approximationDelta
      (RawSupplyNumerics.dyadicTailExponent d)
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (data.A₁.card : ℝ) / (-S).card := by
    simpa [S] using
      supported_ratio_lower_of_hierarchy H z data hdelta
        (RawSupplyNumerics.dyadicSiftedAlpha_pos d).le halpha_le
  have htailPos :
      0 < RawSupplyNumerics.dyadicTailExponent d := by
    unfold RawSupplyNumerics.dyadicTailExponent
    exact RawSupplyNumerics.tailExponent_pos
      (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hk :
      k ≤ RawSupplyNumerics.dyadicSampleKBound d := by
    dsimp [k]
    unfold RawSupplyNumerics.dyadicSampleKBound
    exact RawSupplyNumerics.localizedAPSampleK_le_sampleKBound
      (-S) data.A₁ halphaPos
      (RawSupplyNumerics.dyadicSiftedAlpha_le_two d) hratio htailPos
  have hsmall :
      ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : ℝ) ≤
        RelativeChangSanders.localChangDimension H.B₀ T (1 / 2) →
      2 * RawSupplyNumerics.approximationDelta +
          (2 / (RawSupplyNumerics.dyadicQQuant d : ℝ) +
            400 * ((max H.B₀.rank 1 : ℕ) : ℝ) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : ℝ) ^ RawSupplyNumerics.dyadicTailExponent d) *
          Real.sqrt
            (((DensityStep.SiftedPopularData.supportedPopularSet
                s.restriction.set (z +ᵥ H.Dbohr.carrier)
                H.Ebohr.carrier p sigma).card : ℝ) /
              data.A₁.card) ≤ approximationError := by
    intro T Delta hDelta
    have houtputs := data.output_nonempty hdelta
    have hSnonempty : S.Nonempty := by
      simpa [S] using data.supportedPopularSet_nonempty hdelta
    apply (dyadic_commuted_hsmall d houtputs.1 hSnonempty
      (by simpa [S] using hratio) hwidth).trans
    exact happroximationError
  apply supportedLocalizedPackage_of_hierarchy s W H data hp hB hdelta
    RawSupplyNumerics.approximationDelta
    RawSupplyNumerics.approximationDelta_pos
    (RawSupplyNumerics.dyadicTailExponent d) htailPos.ne'
    kappa hkappa (RawSupplyNumerics.dyadicQQuant d)
    (by
      unfold RawSupplyNumerics.dyadicQQuant
      exact RawSupplyNumerics.qQuant_pos halphaPos)
    approximationError sizeCost hsmall hB₀rank
  · simpa [k, S] using
      hierarchy_rankBudget_of_dyadic_lower W H data d k halpha_le hk
  · exact hmult
  · exact hcardMultiplier
  · exact hsource

/-- A reusable source-cardinality adapter.  Once an earlier geometric loss
compares the ambient state to B and the single displayed exponential
inequality pays the remaining reciprocal source scale and cell multiplier,
the actual regularized source carrier is large enough for the localized
package. -/
theorem source_card_of_inv_scale_and_budget
    (B : BohrData G) (source : Finset G) {rho : NNReal}
    (P : ℕ) (hP : 0 < P)
    (hrho : ((P : NNReal)⁻¹) ≤ rho)
    {baseCard globalLoss sizeCost : ℝ} {cardMultiplier : ℕ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : baseCard ≤ globalLoss * (B.carrier.card : ℝ))
    (hsource : source = (B.dilate rho).carrier)
    (hbudget :
      Real.exp (-sizeCost) * globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (cardMultiplier : ℝ) ≤ 1) :
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
      (source.card : ℝ) := by
  have hBsourceNat :
      B.carrier.card ≤ (3 * P) ^ B.rank * source.card := by
    rw [hsource]
    exact RawSupplyNumerics.card_unit_le_three_mul_pow_rank_mul_card_dilate_of_inv_nat_le
      B P hP hrho
  have hBsource :
      (B.carrier.card : ℝ) ≤
        (((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ) := by
    exact_mod_cast hBsourceNat
  have hbaseSource :
      baseCard ≤ globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ) := by
    calc
      baseCard ≤ globalLoss * (B.carrier.card : ℝ) := hbase
      _ ≤ globalLoss *
          ((((3 * P) ^ B.rank : ℕ) : ℝ) * (source.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hBsource hglobalLoss
      _ = globalLoss * (((3 * P) ^ B.rank : ℕ) : ℝ) *
          (source.card : ℝ) := by ring
  calc
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
        Real.exp (-sizeCost) *
          (globalLoss * (((3 * P) ^ B.rank : ℕ) : ℝ) *
            (source.card : ℝ)) * (cardMultiplier : ℝ) := by
              gcongr
    _ = (Real.exp (-sizeCost) * globalLoss *
          (((3 * P) ^ B.rank : ℕ) : ℝ) * (cardMultiplier : ℝ)) *
          (source.card : ℝ) := by ring
    _ ≤ 1 * (source.card : ℝ) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = (source.card : ℝ) := by ring

/-- Apply the preceding source adapter to the actual nested local-Chang
regular datum and the fixed dyadic hierarchy width. -/
theorem source_card_of_localChang_hierarchy
    (H : SmoothingHierarchy W) (d rankCap : ℕ)
    (T : Finset G) (rho : NNReal) (C₀ : BohrData G)
    (hrho : 1 / 2 ≤ rho)
    (hC₀ : C₀ = H.B₀.dilate (rho *
      RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2)))
    {baseCard globalLoss sizeCost : ℝ} {cardMultiplier : ℕ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : baseCard ≤ globalLoss * (H.B₀.carrier.card : ℝ))
    (hbudget :
      Real.exp (-sizeCost) * globalLoss *
          (((3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
              (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
              (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank : ℕ) : ℝ) *
            (cardMultiplier : ℝ) ≤ 1) :
    Real.exp (-sizeCost) * baseCard * (cardMultiplier : ℝ) ≤
      ((C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier.card : ℝ) := by
  let m := dyadicHierarchyDenominator d rankCap
  let P := RawSupplyNumerics.sourceDenominator H.B₀.rank
    (RelativeChangSanders.localChangCap H.B₀ T (1 / 2)) m
  have hm : 0 < m := by
    simpa [m] using dyadicHierarchyDenominator_pos d rankCap
  have hP : 0 < P := by
    exact RawSupplyNumerics.sourceDenominator_pos hm
  have hscale :
      ((P : NNReal)⁻¹) ≤
        rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
          (m : NNReal)⁻¹ := by
    simpa [P] using
      RawSupplyNumerics.inv_sourceDenominator_le_localChang_source_scale
        H.B₀ T (1 / 2) m hm rho hrho
  have hcarrier :
      (C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier =
        (H.B₀.dilate
          (rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
            (m : NNReal)⁻¹)).carrier := by
    rw [hC₀]
    simp [dyadicHierarchyKappa, m, BohrData.dilate_dilate,
      mul_assoc, mul_comm, mul_left_comm]
  apply source_card_of_inv_scale_and_budget
    (rho := rho * RelativeChangSanders.localChangBaseScale H.B₀ T (1 / 2) *
    (m : NNReal)⁻¹)
    H.B₀ (C₀.dilate (dyadicHierarchyKappa d rankCap)).carrier P hP
  · exact hscale
  · exact hglobalLoss
  · exact hbase
  · exact hcarrier
  · simpa [P, m] using hbudget

/-- Fixed spectral-cell count used by every dyadic localized package at a
given rank cap. -/
def dyadicCellCount (d : ℕ) : ℕ :=
  RawSupplyNumerics.dyadicQQuant d *
    (⌈8 * (RawSupplyNumerics.dyadicRankCost d : ℝ)⌉₊ + 1)

def dyadicCardMultiplier (d rankCap : ℕ) : ℕ :=
  RawSupplyNumerics.cellMultiplier rankCap
    (RawSupplyNumerics.dyadicRankCost d) (dyadicCellCount d)

def dyadicSourceDenominator (d rankCap : ℕ) : ℕ :=
  RawSupplyNumerics.sourceDenominator rankCap
    (RawSupplyNumerics.dyadicRankCost d + 1)
    (dyadicHierarchyDenominator d rankCap)

lemma dyadicCellCount_pos (d : ℕ) : 0 < dyadicCellCount d := by
  unfold dyadicCellCount
  have hq : 0 < RawSupplyNumerics.dyadicQQuant d := by
    unfold RawSupplyNumerics.dyadicQQuant
    exact RawSupplyNumerics.qQuant_pos (RawSupplyNumerics.dyadicSiftedAlpha_pos d)
  positivity

lemma dyadicCardMultiplier_pos (d rankCap : ℕ) :
    0 < dyadicCardMultiplier d rankCap := by
  unfold dyadicCardMultiplier RawSupplyNumerics.cellMultiplier
  have hn := dyadicCellCount_pos d
  positivity

/-- The local Chang cap itself is at most one more than the dyadic rank
budget whenever the hierarchy Croot lower bound is available. -/
theorem hierarchy_localChangCap_le_dyadic
    (W : BohrData G) (H : SmoothingHierarchy W)
    {A B₁ : Finset G} {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData A B₁ H.Ebohr.carrier p sigma delta)
    (hdelta : delta < 1)
    (d k : ℕ)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower A B₁ H.Ebohr.carrier p)
    (hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d)
    (T : Finset G)
    (hT :
      ((hierarchyNegCard data.A₂ ^ k / 2 *
          hierarchySampleCard W H) /
          hierarchyCrootCard W H data.A₂ ^ k ≤ (T.card : ℝ))) :
    RelativeChangSanders.localChangCap H.B₀ T (1 / 2) ≤
      RawSupplyNumerics.dyadicRankCost d + 1 := by
  unfold RelativeChangSanders.localChangCap
  apply Nat.add_le_add_right
  apply Nat.ceil_le.mpr
  exact hierarchy_dimension_le_dyadicRankCost W H data hdelta d k
    halpha_le hk T hT

/-- Fully fixed dyadic localized package from the geometric hierarchy.  The
only remaining input is one scalar exponential budget for the already fixed
global/source/cell loss; all rank, phase, width, and multiplier estimates
are discharged here. -/
theorem supportedLocalizedPackage_of_dyadic_hierarchy_fixed
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    (W : BohrData G) (H : SmoothingHierarchy W)
    {d : ℕ} (z : G)
    {p : ℕ} {sigma delta : ℝ}
    (data : DensityStep.SiftedPopularData s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma delta)
    (hp : 0 < p)
    (hB : ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty)
    (hdelta : delta < 1)
    (halpha_le :
      RawSupplyNumerics.dyadicSiftedAlpha d ≤
        DensityStep.siftingDensityLower s.restriction.set
          (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p)
    (rankCap : ℕ)
    (hB₀rank_s : H.B₀.rank ≤ s.rank)
    (hB₀rank : H.B₀.rank ≤ rankCap)
    {globalLoss localSizeCost : ℝ}
    (hglobalLoss : 0 ≤ globalLoss)
    (hbase : (s.card : ℝ) ≤ globalLoss * (H.B₀.carrier.card : ℝ))
    (hbudget :
      Real.exp (-localSizeCost) * globalLoss *
          (((3 * dyadicSourceDenominator d rankCap) ^ rankCap : ℕ) : ℝ) *
            (dyadicCardMultiplier d rankCap : ℝ) ≤ 1) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (multiplier : ℕ),
      ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
        parentWidth source (RawSupplyNumerics.dyadicRankCost d)
          multiplier (1 / 512 : ℝ),
        P.child.rank ≤ s.rank + RawSupplyNumerics.dyadicRankCost d ∧
        Real.exp (-localSizeCost) * (s.card : ℝ) ≤ P.child.carrier.card := by
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet s.restriction.set
      (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier p sigma
  let k : ℕ := DensityStep.localizedAPSampleK (-S) data.A₁
    RawSupplyNumerics.approximationDelta (RawSupplyNumerics.dyadicTailExponent d)
  have halphaPos := RawSupplyNumerics.dyadicSiftedAlpha_pos d
  have hratio :
      RawSupplyNumerics.dyadicSiftedAlpha d / 2 ≤
        (data.A₁.card : ℝ) / (-S).card := by
    simpa [S] using supported_ratio_lower_of_hierarchy H z data hdelta
      halphaPos.le halpha_le
  have htailPos : 0 < RawSupplyNumerics.dyadicTailExponent d := by
    unfold RawSupplyNumerics.dyadicTailExponent
    exact RawSupplyNumerics.tailExponent_pos halphaPos
      (RawSupplyNumerics.dyadicSiftedAlpha_le_one d)
  have hk : k ≤ RawSupplyNumerics.dyadicSampleKBound d := by
    dsimp [k]
    unfold RawSupplyNumerics.dyadicSampleKBound
    exact RawSupplyNumerics.localizedAPSampleK_le_sampleKBound
      (-S) data.A₁ halphaPos (RawSupplyNumerics.dyadicSiftedAlpha_le_two d)
      hratio htailPos
  apply supportedLocalizedPackage_of_dyadic_hierarchy s W H z data hp hB hdelta
    halpha_le (dyadicHierarchyKappa d rankCap)
    (two_dyadicHierarchyKappa_le_rank_scale d rankCap H.B₀.rank hB₀rank)
    (1 / 512 : ℝ) localSizeCost (le_rfl)
    (dyadicHierarchyKappa_width d rankCap H.B₀.rank hB₀rank)
    hB₀rank_s
  · intro T Delta hT hDelta
    simpa [dyadicCardMultiplier, dyadicCellCount, k, S] using
      hierarchy_cellMultiplier_le_dyadic W H data hdelta d k rankCap
        halpha_le hk hB₀rank T Delta (by simpa [k, S] using hT) hDelta
  · exact dyadicCardMultiplier_pos d rankCap
  · intro T rho C₀ Delta hT hrhoHalf hC₀
    have hcap :
        RelativeChangSanders.localChangCap H.B₀ T (1 / 2) ≤
          RawSupplyNumerics.dyadicRankCost d + 1 :=
      hierarchy_localChangCap_le_dyadic W H data hdelta d k halpha_le hk T
        (by simpa [k, S] using hT)
    have hP :
        RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap) ≤
          dyadicSourceDenominator d rankCap := by
      unfold dyadicSourceDenominator RawSupplyNumerics.sourceDenominator
      have hmax : max H.B₀.rank 1 ≤ max rankCap 1 :=
        max_le_max_right 1 hB₀rank
      gcongr
    have hpow :
        (3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank ≤
          (3 * dyadicSourceDenominator d rankCap) ^ rankCap := by
      calc
        (3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
            (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
            (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank ≤
          (3 * dyadicSourceDenominator d rankCap) ^ H.B₀.rank := by
            apply Nat.pow_le_pow_left
            gcongr
        _ ≤ (3 * dyadicSourceDenominator d rankCap) ^ rankCap := by
          apply Nat.pow_le_pow_right
          · have hPfixed : 0 < dyadicSourceDenominator d rankCap := by
              unfold dyadicSourceDenominator
              exact RawSupplyNumerics.sourceDenominator_pos
                (dyadicHierarchyDenominator_pos d rankCap)
            exact Nat.mul_pos (by norm_num) hPfixed
          · exact hB₀rank
    have hbudget' :
        Real.exp (-localSizeCost) * globalLoss *
          (((3 * RawSupplyNumerics.sourceDenominator H.B₀.rank
              (RelativeChangSanders.localChangCap H.B₀ T (1 / 2))
              (dyadicHierarchyDenominator d rankCap)) ^ H.B₀.rank : ℕ) : ℝ) *
            (dyadicCardMultiplier d rankCap : ℝ) ≤ 1 := by
      apply le_trans ?_ hbudget
      gcongr
    exact source_card_of_localChang_hierarchy H d rankCap T rho C₀
      hrhoHalf hC₀ hglobalLoss hbase hbudget'

/-- Support-restricted rank-regular high-norm step.  This is the version
used with the relative-T package, where the popular set is intersected with
the actual base-pair difference support before Croot--Sisask is invoked. -/
theorem highSmoothingNorm_rankRegularLocatedIncrement_supported
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm sizeCost : ℝ}
    {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) r)
    (hgain :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        lowerNorm ≤
          ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
            r, μ (z +ᵥ E) ○ᵈ μ D] →
        ∀ data : DensityStep.SiftedPopularData s.restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : ℕ),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source rankCost cardMultiplier approximationError,
              P.child.rank ≤ s.rank + rankCost ∧
              Real.exp (-sizeCost) * (s.card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
      BohrStopping.IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
        s.restriction t.located.restriction := by
  obtain ⟨z, hz, hinter, hlocalNorm⟩ :=
    DensityStep.exists_translated_difference_lpNorm_ge hD hE
      s.restriction.nonempty hr hlowerNorm hhigh
  let B₁ : Finset G := z +ᵥ E
  let B₂ : Finset G := D
  have hB : (B₁ ∩ B₂).Nonempty := by
    simpa [B₁, B₂] using hinter
  obtain ⟨data⟩ :=
    DensityStep.exists_sifted_popular_data_unconditional
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      B₁ B₂ hsigma hsigmaOne hdelta hrEven hrTwo hrTail hB
      s.restriction.nonempty
  obtain ⟨parent, parentWidth, source, cardMultiplier, P, hPrank, hPcard⟩ :=
    hlocalized z hz (by simpa [B₁, B₂] using hinter)
      (by simpa [B₁, B₂] using hlocalNorm)
      (by simpa [B₁, B₂] using data)
  have houtputs := data.output_nonempty hdeltaOne
  let S : Finset G :=
    DensityStep.SiftedPopularData.supportedPopularSet
      s.restriction.set B₁ B₂ r sigma
  have hmass :
      1 - delta - approximationError ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.sumConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
            (LocalizedAlmostPeriodicity.differenceConvolution
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    exact DensityStep.smoothed_popular_mass_lower_bound houtputs.1 houtputs.2
      (by
        simpa only [DensityStep.countingInner_difference_setIndicator_eq_sum]
          using data.supported_popular_mass)
      (by simpa [S] using P.triple_error)
  have hthreshold : 0 ≤ (1 - sigma) * lowerNorm :=
    mul_nonneg (sub_nonneg.mpr hsigmaOne) hlowerNorm
  have hpopular : ∀ x ∈ S,
      (1 - sigma) * lowerNorm ≤
        (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x hx
    have hxGlobal : x ∈ _root_.Erdos140.s r sigma B₁ B₂ s.restriction.set := by
      have hx' := hx
      change x ∈ _root_.Erdos140.s r sigma B₁ B₂ s.restriction.set ∩ (B₁ - B₂) at hx'
      exact (Finset.mem_inter.mp hx').1
    have hxPopular :
        (1 - sigma) *
            ‖μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set‖_[
              r, μ B₁ ○ᵈ μ B₂] <
          (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x :=
      (mem_s'.mp hxGlobal)
    exact (mul_le_mul_of_nonneg_left hlocalNorm
      (sub_nonneg.mpr hsigmaOne)).trans hxPopular.le
  have hcorr : ∀ x, 0 ≤
      (μ_[ℝ] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
  obtain ⟨x, hx⟩ :=
    DensityStep.exists_localDensity_ge_of_smoothed_superlevel
      P.child.carrier_nonempty houtputs.1 houtputs.2 s.restriction.nonempty
      hthreshold hcorr hpopular hmass
      (show ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) ≤
          ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) from le_rfl)
  obtain ⟨child, hchildBohr, hchildOuter, hchildCarrier⟩ :=
    DensityStep.RegularChild.exists_of_rankRegular P.child P.child_regular
  have hx' :
      (1 + epsilon / 32) * s.density ≤
        localDensity s.restriction.set child.carrier x := by
    rw [hchildCarrier]
    exact hgain.trans hx
  have hpos : 0 < localDensity s.restriction.set child.carrier x :=
    (mul_pos (by nlinarith [hepsilon]) s.density_pos).trans_le hx'
  let t := DensityStep.narrowLocated s child x hpos
  refine ⟨{ located := t, outer_one := ?_, rankRegular := ?_ }, ?_⟩
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
      using hchildOuter
  · simpa [t, DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
      hchildBohr] using P.child_regular
  · apply DensityStep.narrowLocated_isControlledIncrement s child x hpos hx'
    · simpa [hchildBohr] using hPrank
    · simpa [hchildCarrier] using hPcard

/-- Compose the rank-regular supported high-norm step on the endpoint fibre
with the first reciprocal-child loss.  This is the exact shape required by
the raw two-Bohr endpoint interface. -/
theorem highNorm_endpoint_rankRegular_increment_of_supportedPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilonDense : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilonDense)
    (hepsilonDense_lt_one : epsilonDense < 1)
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm firstSizeCost
      localSizeCost : ℝ} {rankCost r : ℕ}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hfirst :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real]
          (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set
          ○ᵈ
          μ (endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one).restriction.set)
        r)
    (hgain :
      (1 + epsilon / 32) *
          (endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).density ≤
        ((endpointLocated s C.childOne C.childTwo hdense
            hepsilonDense_lt_one).restriction.set.card : ℝ) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        lowerNorm ≤
          ‖μ_[ℝ]
              (endpointLocated s C.childOne C.childTwo hdense
                hepsilonDense_lt_one).restriction.set ○ᵈ
              μ (endpointLocated s C.childOne C.childTwo hdense
                hepsilonDense_lt_one).restriction.set‖_[
            r, μ (z +ᵥ E) ○ᵈ μ D] →
        ∀ data : DensityStep.SiftedPopularData
            (endpointLocated s C.childOne C.childTwo hdense
              hepsilonDense_lt_one).restriction.set
            (z +ᵥ E) D r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source rankCost cardMultiplier approximationError,
              P.child.rank ≤
                (endpointLocated s C.childOne C.childTwo hdense
                  hepsilonDense_lt_one).rank + rankCost ∧
              Real.exp (-localSizeCost) *
                  ((endpointLocated s C.childOne C.childTwo hdense
                    hepsilonDense_lt_one).card : ℝ) ≤ P.child.carrier.card) :
    ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
      (1 + epsilon / 32) * densePairDensity s epsilonDense ≤ t.density ∧
      t.rank ≤ s.rank + rankCost ∧
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) ≤
        (t.card : ℝ) := by
  let u := endpointLocated s C.childOne C.childTwo hdense hepsilonDense_lt_one
  obtain ⟨t, ht⟩ :=
    highSmoothingNorm_rankRegularLocatedIncrement_supported u hD hE hepsilon
      hsigma hsigmaOne hdelta hdeltaOne hr hrEven hrTwo hrTail hlowerNorm
      (by simpa [u] using hhigh) (by simpa [u] using hgain)
      (by simpa [u] using hlocalized)
  have huDensity : densePairDensity s epsilonDense ≤ u.density := by
    let x := GroupCount.densePairPoint hdense
    have hx : densePairDensity s epsilonDense ≤
        localDensity s.restriction.set C.childOne.carrier x := by
      simpa [x, densePairDensity] using
        GroupCount.densePairPoint_density_one hdense
    simpa [u, endpointLocated, DensityStep.density_narrowLocated] using hx
  have hfirst' :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ (u.card : ℝ) := by
    change Real.exp (-firstSizeCost) * (s.card : ℝ) ≤
      (C.childOne.carrier.card : ℝ)
    exact hfirst
  refine ⟨t, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left huDensity (by nlinarith)).trans ht.1
  · have huRank : u.rank = s.rank := by
      simpa [u, endpointLocated, DensityStep.LocatedRestriction.rank,
        BohrStopping.RegularRestriction.rank,
        DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
        using C.rankOne
    rw [← huRank]
    exact ht.2.1
  · calc
      Real.exp (-(firstSizeCost + localSizeCost)) * (s.card : ℝ) =
          Real.exp (-localSizeCost) *
            (Real.exp (-firstSizeCost) * (s.card : ℝ)) := by
        rw [show -(firstSizeCost + localSizeCost) =
            -localSizeCost + -firstSizeCost by ring, Real.exp_add]
        ring
      _ ≤ Real.exp (-localSizeCost) * (u.card : ℝ) :=
        mul_le_mul_of_nonneg_left hfirst' (Real.exp_pos _).le
      _ ≤ (t.card : ℝ) := ht.2.2

end EndpointHighNorm

/-! ## Raw two-Bohr endpoint data -/

section TwoBohr

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The scaled balanced convolution used by the Holder endpoint. -/
def scaledBalanced (K : BohrData G) (A : Finset G) : G → ℝ :=
  (Fintype.card G : ℝ) •
    normalizedConvolution (μ_[ℝ] A - μ K.carrier) (μ A - μ K.carrier)

/-- The two-scale doubled-middle inclusion discharges the Holder
approximation field for the actual endpoint and middle fibres. -/
theorem approximation_of_twoScaleDensePair
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hkappa :
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal))
    (hwidth :
      2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹) :
    |(GroupCount.normalizedMixedProgression
          (endpointSet s C.childOne C.childTwo hdense)
          (middleSet s C.childOne C.childTwo hdense) -
        (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced C.childOne.bohr
            (endpointSet s C.childOne C.childTwo hdense))
          (GroupCount.doubledFinset
            (middleSet s C.childOne C.childTwo hdense))| ≤
      ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8 := by
  let alpha := densePairDensity s epsilon
  have halpha : 0 < alpha :=
    mul_pos (sub_pos.mpr hepsilon_lt_one) s.density_pos
  have hOne : alpha ≤
      localDensity s.restriction.set C.childOne.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_one hdense
  have hTwo : alpha ≤
      localDensity s.restriction.set C.childTwo.carrier
        (GroupCount.densePairPoint hdense) := by
    simpa [alpha, densePairDensity] using
      GroupCount.densePairPoint_density_two hdense
  have hA :
      (endpointSet s C.childOne C.childTwo hdense).Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      C.childOne.carrier_nonempty
    exact halpha.trans_le hOne
  have hA'' :
      (middleSet s C.childOne C.childTwo hdense).Nonempty := by
    apply DensityStep.narrowingSet_nonempty_of_localDensity_pos
      C.childTwo.carrier_nonempty
    exact halpha.trans_le hTwo
  have hAK :
      endpointSet s C.childOne C.childTwo hdense ⊆
        C.childOne.bohr.carrier := by
    rw [← C.childOne_carrier]
    exact DensityStep.narrowingSet_subset_carrier
      (B := C.childOne.bohr) (rho := C.childOne.outer)
      (A := s.restriction.set) (C := C.childOne.carrier)
      (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)
  have hmiddle :
      middleSet s C.childOne C.childTwo hdense ⊆ C.childTwo.carrier := by
    exact DensityStep.narrowingSet_subset_carrier
      (B := C.childTwo.bohr) (rho := C.childTwo.outer)
      (A := s.restriction.set) (C := C.childTwo.carrier)
      (x := GroupCount.densePairPoint hdense) (fun _ hz ↦ hz)
  have hsmall :
      GroupCount.doubledFinset
          (middleSet s C.childOne C.childTwo hdense) ⊆
        (C.childOne.bohr.dilate
          ((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)).carrier :=
    (GroupCount.doubledFinset_mono hmiddle).trans C.doubled_middle_small
  have h :=
    HolderApproximation.normalizedMixedProgression_scaledBalanced_approximation_of_boundaryWidth
      C.childOne_rankRegular hkappa hA hAK hA'' hsmall hwidth
  simpa [scaledBalanced, C.childOne_carrier] using h

/-- Bridge the concrete two-scale geometry to the exact raw endpoint
interface exported by FinalAssembly.

The inputs after the doubled-weight datum are precisely the local analytic
objects still produced by the terminal construction: two smoothing sets,
their support and boundary estimates, and the genuine rank-regular
high-norm exit.  The theorem itself only aligns the two copies of the raw
finite-set definitions and fills the deterministic endpoint fields. -/
theorem finalRawTwoBohrEndpointPackage_of_twoScale
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {mOne mTwo : ℕ} (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {epsilon sizeCost : ℝ} {rankCost p : ℕ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo epsilon sizeCost)
    (hdense : DensityStep.HasDensePair s.located
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := rankCost) s hmOne hmTwo C hnum).childOne
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := rankCost) s hmOne hmTwo C hnum).childTwo epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (W : BohrData G) (hWreg : W.IsRankRegular)
    (hWcarrier :
      W.carrier = GroupCount.doubledFinset C.childTwo.carrier)
    {eta : ℝ≥0} (heta : 0 < eta)
    (hetaNarrow :
      4 * eta ≤ 1 / (400 * (max W.rank 1 : ℕ) : ℝ≥0))
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hDsmall : D ⊆ (W.dilate eta).carrier)
    (hEsmall : E ⊆ (W.dilate eta).carrier)
    {kappa : ℝ≥0}
    (hkappaEq :
      kappa = (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹)
    (hkappa :
      kappa ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : ℝ≥0))
    (hsupport :
      ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
        t ∈ (C.childOne.bohr.dilate kappa).carrier)
    (hwidth :
      2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (kappa : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (kappa : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹)
    (hpDensity :
      (2 / 3 : ℝ) ^ p ≤
        GroupCount.densePairDensity s.located epsilon)
    (hhigh :
      (1 + (1 / 8 : ℝ) / 8) *
          (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
            (μ_[ℝ] (FinalAssembly.rawDensePairEndpointSet hdense) ○ᵈ
              μ (FinalAssembly.rawDensePairEndpointSet hdense))
            (BalancedRestriction.stoppingExponent (1 / 8 : ℝ) p) →
        ∃ t : FinalAssembly.RankRegularLocatedRestriction original,
          (257 / 256 : ℝ) *
              GroupCount.densePairDensity s.located epsilon ≤ t.density ∧
          t.rank ≤ s.rank + rankCost ∧
          Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)) :
    Nonempty
      (FinalAssembly.RawTwoBohrEndpointPackage (p := p) s
        (rankRegularNarrowingPackage_of_reciprocalChildren
          (rankCost := rankCost) s hmOne hmTwo C hnum) hdense) := by
  let P := rankRegularNarrowingPackage_of_reciprocalChildren
    (rankCost := rankCost) s hmOne hmTwo C hnum
  change DensityStep.HasDensePair s.located C.childOne C.childTwo epsilon at hdense
  have hendpoint :
      (FinalAssembly.rawDensePairEndpointSet hdense).Nonempty := by
    simpa [FinalAssembly.rawDensePairEndpointSet, endpointSet] using
      endpointSet_nonempty s.located C.childOne C.childTwo hdense hepsilon_lt_one
  have hsubset :
      FinalAssembly.rawDensePairEndpointSet hdense ⊆ C.childOne.bohr.carrier := by
    rw [← C.childOne_carrier]
    simpa [FinalAssembly.rawDensePairEndpointSet, endpointSet] using
      endpointSet_subset_childOne s.located C.childOne C.childTwo hdense
  have happrox :
      |(GroupCount.normalizedMixedProgression
            (FinalAssembly.rawDensePairEndpointSet hdense)
            (FinalAssembly.rawDensePairMiddleSet hdense) -
          (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
          HolderLifting.pairing
            (FinalAssembly.scaledBalanced C.childOne.bohr
              (FinalAssembly.rawDensePairEndpointSet hdense))
            (GroupCount.doubledFinset
              (FinalAssembly.rawDensePairMiddleSet hdense))| ≤
        ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8 := by
    have hholder :
        (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
          1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal) := by
      simpa [hkappaEq] using hkappa
    have hwidthHolder :
        2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
            (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
              (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
          (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
            (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
              (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
          (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
      simpa [hkappaEq] using hwidth
    simpa [FinalAssembly.rawDensePairEndpointSet,
      FinalAssembly.rawDensePairMiddleSet, endpointSet, middleSet,
      FinalAssembly.scaledBalanced, scaledBalanced] using
      approximation_of_twoScaleDensePair s.located C hdense hepsilon_lt_one
        hholder hwidthHolder
  exact ⟨{
    base := C.childOne.bohr
    weight := W
    base_regular := C.childOne_rankRegular
    weight_regular := hWreg
    base_carrier := by
      change C.childOne.bohr.carrier = C.childOne.carrier
      exact C.childOne_carrier.symm
    weight_carrier := hWcarrier
    endpoint_nonempty := hendpoint
    endpoint_subset := hsubset
    eta := eta
    eta_pos := heta
    eta_narrow := hetaNarrow
    D := D
    E := E
    D_nonempty := hD
    E_nonempty := hE
    D_small := hDsmall
    E_small := hEsmall
    kappa := kappa
    rank_width := hkappa
    smoothing_support := hsupport
    boundary_width := hwidth
    density_power := hpDensity
    approximation := happrox
    highNorm_increment := hhigh }⟩

/-- The actual dyadic hierarchy fills the raw endpoint interface once the
two outer volume budgets and the single fixed local budget are supplied.
All analytic choices are now literal constants. -/
theorem finalRawTwoBohrEndpointPackage_of_dyadic_hierarchy
    {original : Finset G}
    (s : FinalAssembly.RankRegularLocatedRestriction original)
    {d rankCap mOne mTwo : ℕ}
    (hmOne : 0 < mOne) (hmTwo : 0 < mTwo)
    (C : ReciprocalChildren s.located.restriction.bohr mOne mTwo)
    {firstSizeCost localSizeCost : ℝ}
    (hnum : ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
      (firstSizeCost + localSizeCost))
    (hfirst :
      Real.exp (-firstSizeCost) * (s.card : ℝ) ≤ C.childOne.carrier.card)
    (hdense : DensityStep.HasDensePair s.located
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum).childOne
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum).childTwo (1 / 512 : ℝ))
    (hscale : 1 / (2 : ℝ) ^ d ≤ s.density)
    (W : BohrData G) (hWreg : W.IsRankRegular)
    (hWcarrier : W.carrier = GroupCount.doubledFinset C.childTwo.carrier)
    (hWcard : W.carrier.card = C.childTwo.carrier.card)
    (hWrank : W.rank = s.rank)
    (H : SmoothingHierarchy W)
    (hsrank : s.rank ≤ rankCap)
    (hkappa :
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
        1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal))
    (hwidth :
      2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
        (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
          (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
            (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
        (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹)
    (hlocalBudget :
      Real.exp (-localSizeCost) *
          ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
            smoothingHierarchyLoss W : ℕ) : ℝ) *
          (((3 * dyadicSourceDenominator (d + 1) rankCap) ^ rankCap : ℕ) : ℝ) *
            (dyadicCardMultiplier (d + 1) rankCap : ℝ) ≤ 1) :
    Nonempty (FinalAssembly.RawTwoBohrEndpointPackage
      (p := RawSupplyNumerics.holderExponent (d + 1)) s
      (rankRegularNarrowingPackage_of_reciprocalChildren
        (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
        s hmOne hmTwo C hnum) hdense) := by
  change DensityStep.HasDensePair s.located C.childOne C.childTwo
    (1 / 512 : ℝ) at hdense
  let u := endpointLocated s.located C.childOne C.childTwo hdense (by norm_num)
  have hranks := smoothingHierarchy_ranks W H
  have hB₀rankEq : H.B₀.rank = s.rank := hranks.2.2.trans hWrank
  have hB₀rankCap : H.B₀.rank ≤ rankCap := by rw [hB₀rankEq]; exact hsrank
  have huRank : u.rank = s.rank := by
    simpa [u, endpointLocated, DensityStep.LocatedRestriction.rank,
      FinalAssembly.RankRegularLocatedRestriction.rank,
      BohrStopping.RegularRestriction.rank,
      DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction]
      using C.rankOne
  have hB₀rankU : H.B₀.rank ≤ u.rank := by
    rw [hB₀rankEq, huRank]
  have huScale : 1 / (2 : ℝ) ^ (d + 1) ≤ u.density := by
    simpa [u] using endpointLocated_on_nextDyadicScale s.located C hdense rfl
      (by norm_num) hscale
  have hbase : (u.card : ℝ) ≤
      ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
          smoothingHierarchyLoss W : ℕ) : ℝ) * (H.B₀.carrier.card : ℝ) := by
    simpa [u] using endpoint_card_le_globalHierarchyLoss s.located hmOne C hdense
      (by norm_num) s.outer_one W H hWcard
  have hlocalized :
      ∀ (z : G), z ∈ H.Ebohr.carrier - H.Dbohr.carrier →
        ((z +ᵥ H.Dbohr.carrier) ∩ H.Ebohr.carrier).Nonempty →
        (65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          ‖μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set‖_[
            RawSupplyNumerics.smoothingExponent (d + 1),
              μ (z +ᵥ H.Dbohr.carrier) ○ᵈ μ H.Ebohr.carrier] →
        ∀ data : DensityStep.SiftedPopularData u.restriction.set
            (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
            (RawSupplyNumerics.smoothingExponent (d + 1))
            (1 / 8192 : ℝ) (1 / 8192 : ℝ),
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : DensityStep.SupportedLocalizedSiftingPackage data parent
              parentWidth source (RawSupplyNumerics.dyadicRankCost (d + 1))
              cardMultiplier (1 / 512 : ℝ),
              P.child.rank ≤ u.rank + RawSupplyNumerics.dyadicRankCost (d + 1) ∧
              Real.exp (-localSizeCost) * (u.card : ℝ) ≤ P.child.carrier.card := by
    intro z hz hinter hlocalNorm data
    have hlocalNorm' :
        (65 / 64 : ℝ) * (C.childOne.bohr.carrier.card : ℝ)⁻¹ ≤
          BalancedRestriction.weightedLpNorm
            ((NNReal.toReal ∘ (μ (z +ᵥ H.Dbohr.carrier) ○ᵈ
              μ H.Ebohr.carrier)) : G → ℝ)
            (μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set)
            (RawSupplyNumerics.smoothingExponent (d + 1)) := by
      rw [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm
        (μ (z +ᵥ H.Dbohr.carrier) ○ᵈ μ H.Ebohr.carrier)
        (μ_[ℝ] u.restriction.set ○ᵈ μ u.restriction.set)
        (RawSupplyNumerics.smoothingExponent_pos (d + 1))]
      exact hlocalNorm
    have halpha :
        RawSupplyNumerics.dyadicSiftedAlpha (d + 1) ≤
          DensityStep.siftingDensityLower u.restriction.set
            (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
            (RawSupplyNumerics.smoothingExponent (d + 1)) :=
      dyadicSiftedAlpha_le_siftingDensity_of_localNorm
        u.restriction.set (z +ᵥ H.Dbohr.carrier) H.Ebohr.carrier
        C.childOne.bohr.carrier (d + 1)
        C.childOne.bohr.carrier_nonempty
        (by
          have hdensity :
              u.density = (u.restriction.set.card : ℝ) /
                C.childOne.bohr.carrier.card := by
            simp only [u, endpointLocated, DensityStep.density_narrowLocated]
            rw [DensityStep.localDensity_eq_card_narrowingSet_div
              C.childOne.carrier_nonempty]
            simp [DensityStep.narrowLocated, DensityStep.RegularChild.asRestriction,
              C.childOne_carrier]
          rwa [← hdensity]) hlocalNorm'
    exact supportedLocalizedPackage_of_dyadic_hierarchy_fixed u W H z data
      (RawSupplyNumerics.smoothingExponent_pos (d + 1)) hinter (by norm_num)
      halpha rankCap hB₀rankU hB₀rankCap (by positivity) hbase hlocalBudget
  apply finalRawTwoBohrEndpointPackage_of_twoScale s hmOne hmTwo C hnum hdense
    (by norm_num) W hWreg hWcarrier H.eta_pos H.eta_narrow
    H.Ebohr.carrier_nonempty H.Dbohr.carrier_nonempty H.E_small H.D_small
    (show (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ =
      (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ from rfl)
    hkappa
    (smoothing_support_of_hierarchy_twoScale s.located C W H hWcarrier)
    hwidth (densePairDensity_power_next_of_dyadic s.located hscale)
  intro hhigh
  obtain ⟨t, htDensity, htRank, htCard⟩ :=
    highNorm_endpoint_rankRegular_increment_of_supportedPackage
      s.located C hdense (by norm_num) H.Ebohr.carrier_nonempty
      H.Dbohr.carrier_nonempty (epsilon := (1 / 8 : ℝ))
      (sigma := (1 / 8192 : ℝ)) (delta := (1 / 8192 : ℝ))
      (approximationError := (1 / 512 : ℝ))
      (lowerNorm := (65 / 64 : ℝ) *
        (C.childOne.bohr.carrier.card : ℝ)⁻¹)
      (firstSizeCost := firstSizeCost) (localSizeCost := localSizeCost)
      (rankCost := RawSupplyNumerics.dyadicRankCost (d + 1))
      (r := RawSupplyNumerics.smoothingExponent (d + 1))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (RawSupplyNumerics.smoothingExponent_pos (d + 1))
      (RawSupplyNumerics.smoothingExponent_even (d + 1))
      (by
        have hpos := RawSupplyNumerics.smoothingExponent_pos (d + 1)
        have heven := RawSupplyNumerics.smoothingExponent_even (d + 1)
        rcases heven with ⟨k, hk⟩
        omega)
      (dyadic_smoothing_tail_bound (d + 1)) (by positivity) hfirst
      (by
        norm_num at hhigh ⊢
        simpa [u, RawSupplyNumerics.smoothingExponent,
          FinalAssembly.rawDensePairEndpointSet, endpointSet,
          rankRegularNarrowingPackage_of_reciprocalChildren] using hhigh)
      (endpoint_dyadic_high_gain s.located C hdense (by norm_num))
      (by simpa [u] using hlocalized)
  exact ⟨t, by norm_num at htDensity ⊢; exact htDensity, htRank, by
    simpa [FinalAssembly.RankRegularLocatedRestriction.card,
      add_comm, add_left_comm, add_assoc] using htCard⟩

/-- Uniform coefficient used by the unconditional raw supply.  The factor
4096 splits evenly into one first-child budget and one localized budget,
and each half pays the shift from d to d+1. -/
def rawSupplyConstant : ℝ :=
  4096 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ)

lemma nextScale_total_log_le_halfSupply
    (d rank cap : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1)))
    (hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost (d + 1)) :
    Real.log (RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  have hlog := RawSupplyNumerics.log_dyadicTotalLossFormula_le_degree_eleven
    (d + 1) rank cap hrank hcap
  have hbase : ((d + 1 + 1 : ℕ) : ℝ) ≤ 2 * ((d + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hpow : ((d + 1 + 1 : ℕ) : ℝ) ^ 11 ≤
      (2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11 := by
    calc
      ((d + 1 + 1 : ℕ) : ℝ) ^ 11 ≤
          (2 * ((d + 1 : ℕ) : ℝ)) ^ 11 :=
        pow_le_pow_left₀ (by positivity) hbase 11
      _ = (2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11 := by rw [mul_pow]
  calc
    Real.log (RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap : ℝ) ≤
        (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
          ((d + 1 + 1 : ℕ) : ℝ) ^ 11 := by simpa using hlog
    _ ≤ (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((2 : ℝ) ^ 11 * ((d + 1 : ℕ) : ℝ) ^ 11) := by gcongr
    _ = 2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by norm_num; ring

lemma nextScale_twoReciprocal_log_le_halfSupply
    (d rank : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1))) :
    Real.log (RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  let cap := RawSupplyNumerics.dyadicRankCost (d + 1) + 1
  have hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost (d + 1) := by
    dsimp [cap]
    have hpos := RawSupplyNumerics.dyadicRankCost_pos (d + 1)
    omega
  have htotal := nextScale_total_log_le_halfSupply d rank cap hrank hcap
  have htwoPos : (0 : ℝ) < RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    exact_mod_cast Nat.mul_pos
      (RawSupplyNumerics.reciprocalLossFormula_pos
        (ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1))))
      (RawSupplyNumerics.reciprocalLossFormula_pos
        (ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1))))
  have hle : RawSupplyNumerics.twoReciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
      (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) ≤
      RawSupplyNumerics.dyadicTotalLossFormula (d + 1) rank cap := by
    unfold RawSupplyNumerics.dyadicTotalLossFormula
    rw [show
      RawSupplyNumerics.twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
          (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) *
          RawSupplyNumerics.smoothingHierarchyLossFormula rank *
          (3 * RawSupplyNumerics.sourceDenominator rank cap
            (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
              (ConcreteNumerics.rankCap (d + 1)
                (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank *
          RawSupplyNumerics.dyadicCellMultiplier (d + 1) =
        RawSupplyNumerics.twoReciprocalLossFormula rank
          (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
          (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) *
          (RawSupplyNumerics.smoothingHierarchyLossFormula rank *
          (3 * RawSupplyNumerics.sourceDenominator rank cap
            (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
              (ConcreteNumerics.rankCap (d + 1)
                (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank *
          RawSupplyNumerics.dyadicCellMultiplier (d + 1)) by ring]
    apply Nat.le_mul_of_pos_right
    have hsmooth : 0 < RawSupplyNumerics.smoothingHierarchyLossFormula rank := by
      unfold RawSupplyNumerics.smoothingHierarchyLossFormula
        RawSupplyNumerics.reciprocalLossFormula
      positivity
    have hsource : 0 <
        (3 * RawSupplyNumerics.sourceDenominator rank cap
          (RawSupplyNumerics.dyadicHierarchyFormula (d + 1)
            (ConcreteNumerics.rankCap (d + 1)
              (RawSupplyNumerics.dyadicRankCost (d + 1))))) ^ rank := by
      unfold RawSupplyNumerics.sourceDenominator RawSupplyNumerics.dyadicHierarchyFormula
      positivity
    have hcell : 0 < RawSupplyNumerics.dyadicCellMultiplier (d + 1) := by
      unfold RawSupplyNumerics.dyadicCellMultiplier RawSupplyNumerics.cellMultiplier
      have hq : 0 < RawSupplyNumerics.dyadicQQuant (d + 1) := by
        unfold RawSupplyNumerics.dyadicQQuant
        exact RawSupplyNumerics.qQuant_pos
          (RawSupplyNumerics.dyadicSiftedAlpha_pos (d + 1))
      positivity
    exact Nat.mul_pos (Nat.mul_pos hsmooth hsource) hcell
  exact (Real.log_le_log htwoPos (by exact_mod_cast hle)).trans htotal

lemma nextScale_reciprocal_log_le_halfSupply
    (d rank : ℕ)
    (hrank : rank ≤ ConcreteNumerics.rankCap (d + 1)
      (RawSupplyNumerics.dyadicRankCost (d + 1))) :
    Real.log (RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) : ℝ) ≤
      2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
        ((d + 1 : ℕ) : ℝ) ^ 11 := by
  have htwo := nextScale_twoReciprocal_log_le_halfSupply d rank hrank
  have honePos : (0 : ℝ) < RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    exact_mod_cast RawSupplyNumerics.reciprocalLossFormula_pos
      (ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1)))
  have hle : RawSupplyNumerics.reciprocalLossFormula rank
      (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) ≤
      RawSupplyNumerics.twoReciprocalLossFormula rank
        (ConcreteNumerics.mOne (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1)))
        (ConcreteNumerics.mTwo (d + 1) (RawSupplyNumerics.dyadicRankCost (d + 1))) := by
    unfold RawSupplyNumerics.twoReciprocalLossFormula
    apply Nat.le_mul_of_pos_right
    exact RawSupplyNumerics.reciprocalLossFormula_pos
      (ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos (d + 1)))
  exact (Real.log_le_log honePos (by exact_mod_cast hle)).trans htwo

/-- The preceding geometry and dyadic bookkeeping give the unconditional
rank-regular raw supply consumed by the final recursion. -/
theorem exists_rawConcreteSupply :
    ∃ K : ℝ, 0 < K ∧ FinalAssembly.RawConcreteSupply K := by
  refine ⟨rawSupplyConstant, ?_, ?_⟩
  · unfold rawSupplyConstant
    unfold RawSupplyNumerics.dyadicTotalLogConstant
      RawSupplyNumerics.dyadicRankDegreeEightConstant
      RawSupplyNumerics.dyadicCellLogConstant
    positivity
  · intro N A hA d hd
    let e : ℕ := d + 1
    let rankCost : ℕ := RawSupplyNumerics.dyadicRankCost e
    let p : ℕ := RawSupplyNumerics.holderExponent e
    refine ⟨rankCost, p, ?_, ?_⟩
    · dsimp [p]
      exact RawSupplyNumerics.holderExponent_pos e
    · intro n hn s hscale hrank
      let rankCap : ℕ := ConcreteNumerics.rankCap e rankCost
      let mOne : ℕ := ConcreteNumerics.mOne e rankCost
      let mTwo : ℕ := ConcreteNumerics.mTwo e rankCost
      let halfCost : ℝ :=
        2048 * (RawSupplyNumerics.dyadicTotalLogConstant : ℝ) *
          ((d + 1 : ℕ) : ℝ) ^ 11
      have hrankCost : 0 < rankCost := by
        dsimp [rankCost]
        exact RawSupplyNumerics.dyadicRankCost_pos e
      have hsrank : s.rank ≤ rankCap := by
        dsimp [rankCap, e, rankCost]
        unfold ConcreteNumerics.rankCap
        have hn' : n ≤ 1024 * (d + 1 + 1) := by omega
        exact le_trans hrank (Nat.mul_le_mul_right _ hn')
      have hmOne : 0 < mOne := by
        dsimp [mOne]
        exact ConcreteNumerics.mOne_pos hrankCost
      have hmTwo : 0 < mTwo := by
        dsimp [mTwo]
        exact ConcreteNumerics.mTwo_pos hrankCost
      have hscaleE : 1 / (2 : ℝ) ^ e ≤ s.density := by
        calc
          1 / (2 : ℝ) ^ e ≤ 1 / (2 : ℝ) ^ d := by
            dsimp [e]
            rw [pow_succ]
            have hpow : (0 : ℝ) < (2 : ℝ) ^ d := by positivity
            field_simp
            nlinarith
          _ ≤ s.density := hscale
      have hnum : ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
          (rawSupplyConstant * ((d + 1 : ℕ) : ℝ) ^ 11) := by
        refine
          { outer_eq_one := s.outer_one
            rankRegular := s.rankRegular
            scale_rank := ?_
            scale_density := ?_
            card_budget_one := ?_
            card_budget_two := ?_ }
        · dsimp [mOne]
          exact ConcreteNumerics.inv_mOne_le_rank_scale hrankCost hsrank
        · dsimp [mOne]
          exact ConcreteNumerics.mOne_scale_density hrankCost hsrank hscaleE
        ·
          have hloss :
              (0 : ℝ) <
                (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
            unfold reciprocalLoss
            positivity
          apply card_budget_of_log_loss s.located s.outer_one hloss
          have hlog := nextScale_reciprocal_log_le_halfSupply d s.rank hsrank
          apply hlog.trans
          unfold rawSupplyConstant
          gcongr
          norm_num
        ·
          have hloss :
              (0 : ℝ) <
                (twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℕ) := by
            unfold twoReciprocalLoss reciprocalLoss
            positivity
          apply card_budget_of_log_loss s.located s.outer_one hloss
          have hlog := nextScale_twoReciprocal_log_le_halfSupply d s.rank hsrank
          apply hlog.trans
          unfold rawSupplyConstant
          gcongr
          norm_num
      have hmTwoInv : ((mTwo : NNReal)⁻¹) ≤ 1 := by
        apply (inv_le_one₀ (by exact_mod_cast hmTwo)).2
        exact_mod_cast (show 1 ≤ mTwo by omega)
      let C : ReciprocalChildren s.located.restriction.bohr mOne mTwo :=
        Classical.choice (exists_reciprocalChildren s.located.restriction.bohr
          mOne mTwo hmOne hmTwo hmTwoInv)
      have hcost :
          halfCost + halfCost =
            rawSupplyConstant * ((d + 1 : ℕ) : ℝ) ^ 11 := by
        dsimp [halfCost, rawSupplyConstant]
        ring
      have hnumHalf :
          ReciprocalStepBounds s.located mOne mTwo (1 / 512 : ℝ)
            (halfCost + halfCost) := by
        rw [hcost]
        exact hnum
      rw [← hcost]
      let P : FinalAssembly.RankRegularNarrowingPackage s (1 / 512 : ℝ)
          (halfCost + halfCost) rankCost :=
        rankRegularNarrowingPackage_of_reciprocalChildren
          (rankCost := rankCost) s hmOne hmTwo C hnumHalf
      refine ⟨P, ?_⟩
      intro hdense
      have hfirstBudget :
          Real.exp (-halfCost) * (s.located.card : ℝ) ≤
            ((reciprocalLoss s.located.restriction.bohr mOne : ℕ) : ℝ)⁻¹ *
              (s.located.restriction.bohr.carrier.card : ℝ) := by
        have hloss :
            (0 : ℝ) <
              (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
          unfold reciprocalLoss
          positivity
        apply card_budget_of_log_loss s.located s.outer_one hloss
        simpa [halfCost, reciprocalLoss,
          RawSupplyNumerics.reciprocalLossFormula, mOne, e, rankCost,
          FinalAssembly.RankRegularLocatedRestriction.rank,
          DensityStep.LocatedRestriction.rank,
          BohrStopping.RegularRestriction.rank] using
          (nextScale_reciprocal_log_le_halfSupply d s.rank hsrank)
      have hfirst :
          Real.exp (-halfCost) * (s.card : ℝ) ≤ C.childOne.carrier.card := by
        have hloss :
            (0 : ℝ) <
              (reciprocalLoss s.located.restriction.bohr mOne : ℕ) := by
          unfold reciprocalLoss
          positivity
        have hvol :
            (s.located.restriction.bohr.carrier.card : ℝ) ≤
              (reciprocalLoss s.located.restriction.bohr mOne : ℝ) *
                (C.childOne.carrier.card : ℝ) := by
          exact_mod_cast C.cardOne
        simpa [FinalAssembly.RankRegularLocatedRestriction.card] using
          child_card_of_loss s.located hloss hfirstBudget hvol
      letI : NeZero (intervalModulus N) := ⟨by simp [intervalModulus]⟩
      have hodd : Odd (intervalModulus N) := by
        exact ⟨N, by simp [intervalModulus, two_mul]⟩
      let W : BohrData (ZMod (intervalModulus N)) :=
        GroupCount.doubledBohrData (intervalModulus N) hodd C.childTwo.bohr
      have hWreg : W.IsRankRegular := by
        dsimp [W]
        exact doubledBohrData_rankRegular hodd C.childTwo.bohr
          C.childTwo_rankRegular
      have hWcarrier :
          W.carrier = GroupCount.doubledFinset C.childTwo.carrier := by
        rw [C.childTwo_carrier]
        dsimp [W]
        exact
          (GroupCount.doubledFinset_bohrCarrier_eq_doubledBohrData
            hodd C.childTwo.bohr).symm
      have hWcard : W.carrier.card = C.childTwo.carrier.card := by
        dsimp [W]
        rw [GroupCount.card_doubledBohrData_carrier]
        exact congrArg Finset.card C.childTwo_carrier.symm
      have hWrank : W.rank = s.rank := by
        dsimp [W]
        rw [GroupCount.rank_doubledBohrData, C.rankTwo]
        rfl
      let H : SmoothingHierarchy W :=
        Classical.choice (exists_smoothingHierarchy W)
      have hkappa :
          (mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ ≤
            1 / (100 * (max C.childOne.bohr.rank 1 : ℕ) : NNReal) := by
        rw [C.rankOne]
        simpa [mTwo, e, rankCost,
          FinalAssembly.RankRegularLocatedRestriction.rank,
          DensityStep.LocatedRestriction.rank,
          BohrStopping.RegularRestriction.rank] using
          (ConcreteNumerics.two_inv_mTwo_le_rank_scale hrankCost hsrank)
      have hwidth :
          2 * (((endpointSet s.located C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
              (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
                (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ))) +
            (C.childOne.bohr.carrier.card : ℝ)⁻¹ *
              (200 * ((max C.childOne.bohr.rank 1 : ℕ) : ℝ) *
                (((mTwo : NNReal)⁻¹ + (mTwo : NNReal)⁻¹ : NNReal) : ℝ)) ≤
            (1 / 8 : ℝ) / 8 * (C.childOne.bohr.carrier.card : ℝ)⁻¹ := by
        simpa [mTwo, e, rankCost] using
          (dyadic_boundary_width s.located C hdense hscale hsrank hrankCost)
      let cap : ℕ := rankCost + 1
      have hcap : cap ≤ 8 * RawSupplyNumerics.dyadicRankCost e := by
        dsimp [cap, rankCost]
        have hpos := RawSupplyNumerics.dyadicRankCost_pos e
        omega
      have htotalPos :
          0 < RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap := by
        have hmOne' : 0 < ConcreteNumerics.mOne e
            (RawSupplyNumerics.dyadicRankCost e) :=
          ConcreteNumerics.mOne_pos (RawSupplyNumerics.dyadicRankCost_pos e)
        have hmTwo' : 0 < ConcreteNumerics.mTwo e
            (RawSupplyNumerics.dyadicRankCost e) :=
          ConcreteNumerics.mTwo_pos (RawSupplyNumerics.dyadicRankCost_pos e)
        have hq : 0 < RawSupplyNumerics.dyadicQQuant e := by
          unfold RawSupplyNumerics.dyadicQQuant
          exact RawSupplyNumerics.qQuant_pos
            (RawSupplyNumerics.dyadicSiftedAlpha_pos e)
        have htwo : 0 < RawSupplyNumerics.twoReciprocalLossFormula rankCap
            (ConcreteNumerics.mOne e (RawSupplyNumerics.dyadicRankCost e))
            (ConcreteNumerics.mTwo e (RawSupplyNumerics.dyadicRankCost e)) := by
          unfold RawSupplyNumerics.twoReciprocalLossFormula
          exact Nat.mul_pos
            (RawSupplyNumerics.reciprocalLossFormula_pos hmOne')
            (RawSupplyNumerics.reciprocalLossFormula_pos hmTwo')
        have hsmooth :
            0 < RawSupplyNumerics.smoothingHierarchyLossFormula rankCap := by
          unfold RawSupplyNumerics.smoothingHierarchyLossFormula
            RawSupplyNumerics.reciprocalLossFormula
          positivity
        have hsource :
            0 < (3 * RawSupplyNumerics.sourceDenominator rankCap cap
              (RawSupplyNumerics.dyadicHierarchyFormula e
                (ConcreteNumerics.rankCap e
                  (RawSupplyNumerics.dyadicRankCost e)))) ^ rankCap := by
          unfold RawSupplyNumerics.sourceDenominator
            RawSupplyNumerics.dyadicHierarchyFormula
          positivity
        have hcell : 0 < RawSupplyNumerics.dyadicCellMultiplier e := by
          unfold RawSupplyNumerics.dyadicCellMultiplier
            RawSupplyNumerics.cellMultiplier
          positivity
        unfold RawSupplyNumerics.dyadicTotalLossFormula
        exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos htwo hsmooth) hsource) hcell
      have htotalBudget :
          Real.exp (-halfCost) *
              (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) ≤
            1 := by
        apply exp_mul_loss_le_one_of_log_loss htotalPos
        simpa [halfCost, e] using
          (nextScale_total_log_le_halfSupply d rankCap cap (le_rfl) hcap)
      have hfiniteLe :
          (twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
              smoothingHierarchyLoss W) *
              (3 * dyadicSourceDenominator e rankCap) ^ rankCap *
              dyadicCardMultiplier e rankCap ≤
            RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap := by
        have hbohrRank :
            s.located.restriction.bohr.rank ≤ rankCap := by
          simpa [FinalAssembly.RankRegularLocatedRestriction.rank,
            DensityStep.LocatedRestriction.rank,
            BohrStopping.RegularRestriction.rank] using hsrank
        have hreciprocal {m : ℕ} (hm : 0 < m) :
            reciprocalLoss s.located.restriction.bohr m ≤
              RawSupplyNumerics.reciprocalLossFormula rankCap m := by
          unfold reciprocalLoss RawSupplyNumerics.reciprocalLossFormula
          exact Nat.mul_le_mul
            (Nat.pow_le_pow_right (by omega) hbohrRank)
            (Nat.pow_le_pow_right (by norm_num) hbohrRank)
        have htwo :
            twoReciprocalLoss s.located.restriction.bohr mOne mTwo ≤
              RawSupplyNumerics.twoReciprocalLossFormula rankCap mOne mTwo := by
          unfold twoReciprocalLoss RawSupplyNumerics.twoReciprocalLossFormula
          exact Nat.mul_le_mul (hreciprocal hmOne) (hreciprocal hmTwo)
        have hmax : max s.rank 1 ≤ max rankCap 1 :=
          max_le_max_right 1 hsrank
        have hsmoothFactor (c : ℕ) (hc : 0 < c) :
            (3 * (c * max s.rank 1)) ^ s.rank * 4 ^ s.rank ≤
              RawSupplyNumerics.reciprocalLossFormula rankCap
                (c * max rankCap 1) := by
          unfold RawSupplyNumerics.reciprocalLossFormula
          have hbase :
              3 * (c * max s.rank 1) ≤ 3 * (c * max rankCap 1) := by
            gcongr
          have hbasePos : 0 < 3 * (c * max rankCap 1) := by positivity
          have hfirst :
              (3 * (c * max s.rank 1)) ^ s.rank ≤
                (3 * (c * max rankCap 1)) ^ rankCap := by
            calc
              (3 * (c * max s.rank 1)) ^ s.rank ≤
                  (3 * (c * max rankCap 1)) ^ s.rank :=
                Nat.pow_le_pow_left hbase _
              _ ≤ (3 * (c * max rankCap 1)) ^ rankCap :=
                Nat.pow_le_pow_right hbasePos hsrank
          exact Nat.mul_le_mul hfirst
            (Nat.pow_le_pow_right (by norm_num) hsrank)
        have hsmooth :
            smoothingHierarchyLoss W ≤
              RawSupplyNumerics.smoothingHierarchyLossFormula rankCap := by
          unfold smoothingHierarchyLoss
            RawSupplyNumerics.smoothingHierarchyLossFormula
          rw [hWrank]
          exact Nat.mul_le_mul
            (Nat.mul_le_mul (hsmoothFactor 1600 (by norm_num))
              (hsmoothFactor 200 (by norm_num)))
            (hsmoothFactor 200 (by norm_num))
        have hsource :
            (3 * dyadicSourceDenominator e rankCap) ^ rankCap =
              (3 * RawSupplyNumerics.sourceDenominator rankCap cap
                (RawSupplyNumerics.dyadicHierarchyFormula e
                  (ConcreteNumerics.rankCap e
                    (RawSupplyNumerics.dyadicRankCost e)))) ^ rankCap := by
          unfold dyadicSourceDenominator dyadicHierarchyDenominator
            RawSupplyNumerics.sourceDenominator
            RawSupplyNumerics.dyadicHierarchyFormula
            RawSupplyNumerics.dyadicAlphaExponent
          dsimp [rankCap, rankCost, cap]
        have hcell :
            dyadicCardMultiplier e rankCap =
              RawSupplyNumerics.dyadicCellMultiplier e := by
          unfold dyadicCardMultiplier dyadicCellCount
            RawSupplyNumerics.dyadicCellMultiplier
          rw [RawSupplyNumerics.ceil_eight_mul_rank_add_one_eq]
        unfold RawSupplyNumerics.dyadicTotalLossFormula
        rw [← hsource, ← hcell]
        dsimp [mOne, mTwo, rankCost]
        exact Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.mul_le_mul htwo hsmooth) (le_rfl))
          (le_rfl)
      have hlocalBudget :
          Real.exp (-halfCost) *
              ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                smoothingHierarchyLoss W : ℕ) : ℝ) *
              (((3 * dyadicSourceDenominator e rankCap) ^ rankCap : ℕ) : ℝ) *
                (dyadicCardMultiplier e rankCap : ℝ) ≤ 1 := by
        calc
          Real.exp (-halfCost) *
              ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                smoothingHierarchyLoss W : ℕ) : ℝ) *
              (((3 * dyadicSourceDenominator e rankCap) ^ rankCap : ℕ) : ℝ) *
                (dyadicCardMultiplier e rankCap : ℝ) ≤
              Real.exp (-halfCost) *
                (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) := by
                  have hfiniteLeR :
                      ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo *
                        smoothingHierarchyLoss W) *
                        (3 * dyadicSourceDenominator e rankCap) ^ rankCap *
                        dyadicCardMultiplier e rankCap : ℝ) ≤
                        (RawSupplyNumerics.dyadicTotalLossFormula
                          e rankCap cap : ℝ) := by
                    exact_mod_cast hfiniteLe
                  push_cast at hfiniteLeR ⊢
                  calc
                    Real.exp (-halfCost) *
                        ((twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
                          smoothingHierarchyLoss W) *
                        (3 * dyadicSourceDenominator e rankCap : ℝ) ^ rankCap *
                          dyadicCardMultiplier e rankCap =
                        Real.exp (-halfCost) *
                          (((twoReciprocalLoss s.located.restriction.bohr mOne mTwo : ℝ) *
                            smoothingHierarchyLoss W) *
                            (3 * dyadicSourceDenominator e rankCap : ℝ) ^ rankCap *
                              dyadicCardMultiplier e rankCap) := by ring
                    _ ≤ Real.exp (-halfCost) *
                        (RawSupplyNumerics.dyadicTotalLossFormula e rankCap cap : ℝ) :=
                      mul_le_mul_of_nonneg_left hfiniteLeR (Real.exp_pos _).le
          _ ≤ 1 := htotalBudget
      simpa [p, e] using
        (finalRawTwoBohrEndpointPackage_of_dyadic_hierarchy
          (d := d) (rankCap := rankCap) (mOne := mOne) (mTwo := mTwo)
          s hmOne hmTwo C hnumHalf hfirst hdense hscale W hWreg
          hWcarrier hWcard hWrank H hsrank hkappa hwidth hlocalBudget)

/-- The smallest honest two-Bohr endpoint API.

All fields are geometric or analytic estimates on actual objects.  In
particular, it does not contain a Holder certificate or an increment.  The
middle child and its doubled carrier are already present in
ReciprocalChildren; the weight equality below identifies that actual doubled
carrier with the regular Bohr datum used by TwoBohrBalanced. -/
structure RawTwoBohrEndpointPackage
    {original : Finset G} (s : DensityStep.LocatedRestriction original)
    {mOne mTwo : ℕ} (C : ReciprocalChildren s.restriction.bohr mOne mTwo)
    {epsilon : ℝ}
    (hdense : DensityStep.HasDensePair s C.childOne C.childTwo epsilon)
    (p : ℕ) where
  base : BohrData G
  weight : BohrData G
  base_regular : base.IsRankRegular
  weight_regular : weight.IsRankRegular
  base_carrier : base.carrier = C.childOne.carrier
  weight_carrier :
    weight.carrier = GroupCount.doubledFinset C.childTwo.carrier
  eta : ℝ≥0
  eta_pos : 0 < eta
  eta_narrow :
    4 * eta ≤ 1 / (400 * (max weight.rank 1 : ℕ) : ℝ≥0)
  D : Finset G
  E : Finset G
  D_nonempty : D.Nonempty
  E_nonempty : E.Nonempty
  D_small : D ⊆ (weight.dilate eta).carrier
  E_small : E ⊆ (weight.dilate eta).carrier
  kappa : ℝ≥0
  rank_width :
    kappa ≤ 1 / (100 * (max base.rank 1 : ℕ) : ℝ≥0)
  smoothing_support :
    ∀ t, LocalizedUnbalancing.smoothingWeight D E t ≠ 0 →
      t ∈ (base.dilate kappa).carrier
  boundary_width :
    2 * (((endpointSet s C.childOne C.childTwo hdense).card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ))) +
      (base.carrier.card : ℝ)⁻¹ *
        (200 * ((max base.rank 1 : ℕ) : ℝ) * (kappa : ℝ)) ≤
      (1 / 8 : ℝ) / 8 * (base.carrier.card : ℝ)⁻¹
  density_power :
    (2 / 3 : ℝ) ^ p ≤ densePairDensity s epsilon
  approximation :
    |(GroupCount.normalizedMixedProgression
          (endpointSet s C.childOne C.childTwo hdense)
          (middleSet s C.childOne C.childTwo hdense) -
        (Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) -
        HolderLifting.pairing
          (scaledBalanced base (endpointSet s C.childOne C.childTwo hdense))
          (GroupCount.doubledFinset
            (middleSet s C.childOne C.childTwo hdense))| ≤
      ((Fintype.card G : ℝ) / (#C.childOne.carrier : ℝ)) / 8

end TwoBohr

end

end ConcreteSupply

end

/-! ### Upstream module `/tmp/plby-fresh/src/latest/ErdosProblems/Erdos140.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 140.
https://www.erdosproblems.com/forum/thread/140

Informal authors:
- Zachary Kelley
- Raghu Meka

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos140.md
-/

/-!
# Erdős Problem 140

The public theorem below is the literal r3 formulation of the problem:
for every positive real exponent C, the largest three-term-progression-free
subset of {1, ..., N} is O(N / (log N)^C).

The long finite-group argument is split into the files in
ErdosProblems/Erdos140/.  This endpoint first turns the concrete
rank-regular two-Bohr supply into the ordered Kelley--Meka progression count,
then uses the elementary quantitative endpoint from Quantitative.lean.
-/

open _root_.Filter
open scoped _root_.Topology

/-- Once the concrete rank-regular supply has been established, the exact
Erdős-140 asymptotic bound follows for every real logarithmic exponent.
The positivity hypothesis from the problem statement is therefore not needed
at this final analytic step. -/
theorem isBigO_r3_log_rpow_of_rawConcreteSupply
    {K : ℝ} (hK : 0 < K) (hraw : FinalAssembly.RawConcreteSupply K)
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  obtain ⟨K', N₀, hcount⟩ :=
    exists_orderedCount_of_exists_holderCertificates
      ⟨8 + 2050 * (2 : ℝ) ^ 12 * K,
        FinalAssembly.holderCertificates_of_rawConcreteSupply hK hraw⟩
  exact isBigO_r3_log_rpow_of_orderedCount hcount C

/-- Existential form of the final composition.  The remaining structural
theorem in ConcreteSupply.lean supplies this hypothesis unconditionally. -/
theorem erdos_140_of_exists_rawConcreteSupply
    (hraw : ∃ K : ℝ, 0 < K ∧ FinalAssembly.RawConcreteSupply K)
    (C : ℝ) (_hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  obtain ⟨K, hK, hKraw⟩ := hraw
  exact isBigO_r3_log_rpow_of_rawConcreteSupply hK hKraw C

/-- Erdős Problem 140: for every positive logarithmic exponent C, the
largest three-term-progression-free subset of {1, ..., N} is
O(N / (log N)^C). -/
theorem erdos_140 (C : ℝ) (hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  exact erdos_140_of_exists_rawConcreteSupply
    ConcreteSupply.exists_rawConcreteSupply C hC

end

#print axioms erdos_140
-- 'Erdos140.erdos_140' depends on axioms: [propext, Classical.choice, Quot.sound]

-- close scopes leaked by vendored modules whose `namespace X` blocks were re-emitted
-- as `section` + `open X` by the flattener
end
end
end
end
end
end
end

end Erdos140
