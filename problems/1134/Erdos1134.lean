import Mathlib

namespace Erdos1134

set_option maxHeartbeats 800000

/-
# Erdos Problem 1134

Let $A$ be the smallest subset of $\mathbb{N} = \{1, 2, 3, \ldots\}$ such that:
1. $1 \in A$, and
2. for every $x \in A$, the elements $2x + 1$, $3x + 1$, and $6x + 1$ also belong to $A$.

Equivalently, define $A_0 = \{1\}$ and
$A_{n+1} = A_n \cup \{2x+1 \mid x \in A_n\} \cup \{3x+1 \mid x \in A_n\} \cup \{6x+1 \mid x \in A_n\}$
for all $n \ge 0$. Then $A = \bigcup_{n \ge 0} A_n$.

The lower (asymptotic) density of a set $S \subseteq \mathbb{N}$ is
$$\underline{d}(S) := \liminf_{N \to \infty} \frac{|S \cap \{1, 2, \ldots, N\}|}{N}.$$

Erdos Problem 1134 asks: "Does $A$ have positive lower density?"
The answer is no: $\underline{d}(A) = 0$.
-/

inductive ErdosSetA : ℕ → Prop
  | base : ErdosSetA 1
  | double_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (2 * x + 1)
  | triple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (3 * x + 1)
  | sextuple_plus_one (x : ℕ) : ErdosSetA x → ErdosSetA (6 * x + 1)

theorem ErdosSetA.smallest (S : Set ℕ) (h1 : 1 ∈ S)
    (h2 : ∀ x ∈ S, 2 * x + 1 ∈ S)
    (h3 : ∀ x ∈ S, 3 * x + 1 ∈ S)
    (h6 : ∀ x ∈ S, 6 * x + 1 ∈ S) :
    setOf ErdosSetA ⊆ S := by
  intro n hn
  induction hn with
  | base => exact h1
  | double_plus_one x _ ih => exact h2 x ih
  | triple_plus_one x _ ih => exact h3 x ih
  | sextuple_plus_one x _ ih => exact h6 x ih

theorem ErdosSetA.pos {n : ℕ} (h : ErdosSetA n) : 0 < n := by
  induction h with
  | base => omega
  | double_plus_one x _ ih => omega
  | triple_plus_one x _ ih => omega
  | sextuple_plus_one x _ ih => omega

noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)) Filter.atTop

section CanonicalPaths

-- Non-terminal operation type: f₆ or gₖ
inductive NTOp
  | f6 : NTOp                    -- x ↦ 6x + 1, multiplier 6
  | gk : ℕ → NTOp               -- x ↦ (3·2^k)x + (3·2^k - 2), multiplier 3·2^k
deriving DecidableEq

def NTOp.mult : NTOp → ℕ
  | .f6 => 6
  | .gk k => 3 * 2 ^ k

def NTOp.apply : NTOp → ℕ → ℕ
  | .f6, x => 6 * x + 1
  | .gk k, x => 3 * 2 ^ k * x + (3 * 2 ^ k - 2)

-- Apply a list of non-terminal operations left-to-right (leftmost = innermost)
def applyNTOps : List NTOp → ℕ → ℕ
  | [], x => x
  | op :: rest, x => applyNTOps rest (op.apply x)

def ntOpsMult : List NTOp → ℕ
  | [] => 1
  | op :: rest => op.mult * ntOpsMult rest

-- A canonical word: a list of non-terminal ops plus an OUTER terminal f₂ exponent
structure CanonWord where
  ops : List NTOp     -- non-terminal operations (applied first, left-to-right)
  terminal : ℕ        -- OUTER exponent t for terminal f₂^t (applied LAST)

-- Apply a canonical word to input x:
-- First apply the non-terminal ops left-to-right, then apply f₂^t (outer terminal)
def CanonWord.apply (w : CanonWord) (x : ℕ) : ℕ :=
  let y := applyNTOps w.ops x
  2 ^ w.terminal * y + (2 ^ w.terminal - 1)

-- Multiplier of a canonical word
def CanonWord.mult (w : CanonWord) : ℕ :=
  ntOpsMult w.ops * 2 ^ w.terminal

lemma applyNTOps_append (ops1 ops2 : List NTOp) (x : ℕ) :
    applyNTOps (ops1 ++ ops2) x = applyNTOps ops2 (applyNTOps ops1 x) := by
  induction ops1 generalizing x with
  | nil => simp [applyNTOps]
  | cons op rest ih => simp [applyNTOps, ih]

lemma ntOpsMult_append (ops1 ops2 : List NTOp) :
    ntOpsMult (ops1 ++ ops2) = ntOpsMult ops1 * ntOpsMult ops2 := by
  induction ops1 with
  | nil => simp [ntOpsMult]
  | cons op rest ih => simp [ntOpsMult, ih, mul_assoc]

-- Countable instances (needed for Dirichlet series tsum)
instance : Countable NTOp := by
  exact Function.Injective.countable
    (f := fun op => match op with | .f6 => Sum.inl () | .gk k => Sum.inr k)
    (by intro a b h; match a, b with | .f6, .f6 => rfl | .gk m, .gk n => exact congrArg _ (Sum.inr.inj h))

instance : Countable CanonWord :=
  (Equiv.mk (fun w => (w.ops, w.terminal)) (fun p => ⟨p.1, p.2⟩)
    (fun _ => rfl) (fun _ => rfl)).injective.countable

-- Multiplier is always positive
lemma ntOpsMult_pos (ops : List NTOp) : 0 < ntOpsMult ops := by
  induction ops with
  | nil => simp [ntOpsMult]
  | cons op rest ih =>
    simp only [ntOpsMult]
    apply Nat.mul_pos
    · cases op with
      | f6 => decide
      | gk k => exact Nat.mul_pos (by omega) (by positivity)
    · exact ih

lemma canonword_mult_pos (w : CanonWord) : 0 < w.mult := by
  exact Nat.mul_pos (ntOpsMult_pos w.ops) (by positivity)

end CanonicalPaths

lemma f6_f2t_identity (y t' : ℕ) :
    6 * (2 ^ (t' + 1) * y + (2 ^ (t' + 1) - 1)) + 1 =
    4 * (3 * 2 ^ t' * y + (3 * 2 ^ t' - 2)) + 3 := by
  have hp : 1 ≤ 2 ^ t' := Nat.one_le_pow t' 2 (by omega)
  have h1 : 2 ^ (t' + 1) = 2 * 2 ^ t' := by ring
  have h2 : 2 * 2 ^ t' * y = 2 * (2 ^ t' * y) := by ring
  have h3 : 3 * 2 ^ t' * y = 3 * (2 ^ t' * y) := by ring
  have h4 : 3 * 2 ^ t' = 3 * (2 ^ t') := by ring
  rw [h1, h2, h3, h4]
  set p := 2 ^ t'
  omega

lemma canonical_path_exists (a : ℕ) (ha : ErdosSetA a) :
    ∃ w : CanonWord, w.apply 1 = a := by
  induction ha with
  | base =>
    -- a = 1: use ⟨[], 0⟩
    exact ⟨⟨[], 0⟩, by simp [CanonWord.apply, applyNTOps]⟩
  | double_plus_one x _ ih =>
    -- a = 2x+1: increment outer terminal
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    refine ⟨⟨ops, t + 1⟩, ?_⟩
    simp only [CanonWord.apply] at hw ⊢
    set y := applyNTOps ops 1
    set p := 2 ^ t
    have hp : 1 ≤ p := Nat.one_le_pow t 2 (by omega)
    have h1 : 2 ^ (t + 1) = 2 * p := by ring
    rw [h1]
    have h2 : 2 * p * y + (2 * p - 1) = 2 * (p * y + (p - 1)) + 1 := by
      have : 2 * p * y = 2 * (p * y) := by ring
      rw [this]; set q := p * y; omega
    rw [h2, hw]
  | triple_plus_one x _ ih =>
    -- a = 3x+1: absorb outer terminal into gk, reset terminal to 0
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    refine ⟨⟨ops ++ [NTOp.gk t], 0⟩, ?_⟩
    simp only [CanonWord.apply] at hw ⊢
    rw [applyNTOps_append]
    simp only [applyNTOps, NTOp.apply]
    set y := applyNTOps ops 1
    set p := 2 ^ t
    have hp : 1 ≤ p := Nat.one_le_pow t 2 (by omega)
    have h1 : 3 * p * y + (3 * p - 2) = 3 * (p * y + (p - 1)) + 1 := by
      have : 3 * p * y = 3 * (p * y) := by ring
      rw [this]; set q := p * y; omega
    omega
  | sextuple_plus_one x _ ih =>
    -- a = 6x+1: case split on terminal
    obtain ⟨⟨ops, t⟩, hw⟩ := ih
    match t with
    | 0 =>
      -- t = 0: append f6, terminal stays 0
      refine ⟨⟨ops ++ [NTOp.f6], 0⟩, ?_⟩
      simp only [CanonWord.apply] at hw ⊢
      rw [applyNTOps_append]
      simp only [applyNTOps, NTOp.apply]
      omega
    | t' + 1 =>
      -- t ≥ 1: use f6_f2t_identity to get ⟨ops ++ [gk t'], 2⟩
      refine ⟨⟨ops ++ [NTOp.gk t'], 2⟩, ?_⟩
      simp only [CanonWord.apply] at hw ⊢
      rw [applyNTOps_append]
      simp only [applyNTOps, NTOp.apply]
      set y := applyNTOps ops 1
      have hf6 := f6_f2t_identity y t'
      omega

lemma ntop_apply_succ_le (op : NTOp) (x : ℕ) :
    op.apply x + 1 ≤ op.mult * (x + 1) := by
  cases op with
  | f6 => simp [NTOp.apply, NTOp.mult]; omega
  | gk k =>
    simp only [NTOp.apply, NTOp.mult]
    have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    have h2p : 2 ≤ 3 * 2 ^ k := by omega
    have lhs_eq : 3 * 2 ^ k * x + (3 * 2 ^ k - 2) + 1 = 3 * 2 ^ k * x + (3 * 2 ^ k - 1) := by omega
    have rhs_eq : 3 * 2 ^ k * (x + 1) = 3 * 2 ^ k * x + 3 * 2 ^ k := by ring
    rw [lhs_eq, rhs_eq]; omega

lemma ntop_apply_ge (op : NTOp) (x : ℕ) :
    op.mult * x ≤ op.apply x := by
  cases op with
  | f6 => simp [NTOp.apply, NTOp.mult]
  | gk k => simp [NTOp.apply, NTOp.mult]

lemma applyNTOps_succ_le (ops : List NTOp) (x : ℕ) :
    applyNTOps ops x + 1 ≤ ntOpsMult ops * (x + 1) := by
  induction ops generalizing x with
  | nil => simp [applyNTOps, ntOpsMult]
  | cons op rest ih =>
    simp only [applyNTOps, ntOpsMult]
    calc applyNTOps rest (op.apply x) + 1
        ≤ ntOpsMult rest * (op.apply x + 1) := ih (op.apply x)
      _ ≤ ntOpsMult rest * (op.mult * (x + 1)) := Nat.mul_le_mul_left _ (ntop_apply_succ_le op x)
      _ = op.mult * ntOpsMult rest * (x + 1) := by ring

lemma applyNTOps_ge (ops : List NTOp) (x : ℕ) :
    ntOpsMult ops * x ≤ applyNTOps ops x := by
  induction ops generalizing x with
  | nil => simp [applyNTOps, ntOpsMult]
  | cons op rest ih =>
    simp only [applyNTOps, ntOpsMult]
    calc op.mult * ntOpsMult rest * x
        = ntOpsMult rest * (op.mult * x) := by ring
      _ ≤ ntOpsMult rest * op.apply x := Nat.mul_le_mul_left _ (ntop_apply_ge op x)
      _ ≤ applyNTOps rest (op.apply x) := ih (op.apply x)

lemma value_le_twice_mult (w : CanonWord) :
    w.apply 1 + 1 ≤ 2 * w.mult := by
  simp only [CanonWord.apply, CanonWord.mult]
  set y := applyNTOps w.ops 1
  set p := 2 ^ w.terminal
  have hp : 1 ≤ p := Nat.one_le_pow w.terminal 2 (by omega)
  have lhs_eq : p * y + (p - 1) + 1 = p * (y + 1) := by
    have : p * (y + 1) = p * y + p := by ring
    omega
  have rhs_eq : 2 * (ntOpsMult w.ops * p) = p * (2 * ntOpsMult w.ops) := by ring
  rw [lhs_eq, rhs_eq]
  apply Nat.mul_le_mul_left
  have := applyNTOps_succ_le w.ops 1
  linarith

lemma value_ge_mult (w : CanonWord) :
    w.mult ≤ w.apply 1 := by
  simp only [CanonWord.apply, CanonWord.mult]
  set y := applyNTOps w.ops 1
  set p := 2 ^ w.terminal
  have hp : 1 ≤ p := Nat.one_le_pow w.terminal 2 (by omega)
  have hge := applyNTOps_ge w.ops 1
  simp only [mul_one] at hge
  calc ntOpsMult w.ops * p ≤ y * p := Nat.mul_le_mul_right p hge
    _ = p * y := by ring
    _ ≤ p * y + (p - 1) := Nat.le_add_right _ _

lemma rankin_trick {α : Type*} (F : Finset α) (f : α → ℕ) (N : ℕ) (s : ℝ)
    (hs : 0 < s) (hN : 0 < N)
    (hf : ∀ a ∈ F, 0 < f a ∧ f a ≤ N) :
    (F.card : ℝ) ≤ (N : ℝ) ^ s * F.sum (fun a => ((f a : ℝ) ^ (-s))) := by
  calc (F.card : ℝ)
      = F.sum (fun _ => (1 : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ F.sum (fun a => (N : ℝ) ^ s * ((f a : ℝ) ^ (-s))) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨hfa_pos, hfa_le⟩ := hf a ha
        have hfa_cast_pos : (0 : ℝ) < (f a : ℝ) := Nat.cast_pos.mpr hfa_pos
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        rw [le_mul_inv_iff₀ (Real.rpow_pos_of_pos hfa_cast_pos s)]
        rw [one_mul]
        exact Real.rpow_le_rpow (le_of_lt hfa_cast_pos) (Nat.cast_le.mpr hfa_le) (le_of_lt hs)
    _ = (N : ℝ) ^ s * F.sum (fun a => ((f a : ℝ) ^ (-s))) := by
        rw [← Finset.mul_sum]

lemma erdos_injection_canonical (N : ℕ) :
    ∃ (W : Finset CanonWord),
      Set.ncard (setOf ErdosSetA ∩ Set.Iic N) ≤ W.card ∧
      ∀ w ∈ W, 0 < w.mult ∧ w.mult ≤ N := by
  classical
  set S := setOf ErdosSetA ∩ Set.Iic N with hS_def
  have hS_finite : S.Finite := Set.Finite.subset (Set.finite_Iic N) Set.inter_subset_right
  let g : ℕ → CanonWord := fun a =>
    if h : ErdosSetA a then (canonical_path_exists a h).choose else ⟨[], 0⟩
  have g_spec : ∀ a (ha : ErdosSetA a), (g a).apply 1 = a := by
    intro a ha
    change (if h : ErdosSetA a then (canonical_path_exists a h).choose else ⟨[], 0⟩).apply 1 = a
    rw [dif_pos ha]
    exact (canonical_path_exists a ha).choose_spec
  have g_inj : Set.InjOn g S := by
    intro a ha b hb hab
    have ha' : ErdosSetA a := ha.1
    have hb' : ErdosSetA b := hb.1
    have : (g a).apply 1 = (g b).apply 1 := by rw [hab]
    rw [g_spec a ha', g_spec b hb'] at this
    exact this
  have himg_finite : (g '' S).Finite := hS_finite.image g
  refine ⟨himg_finite.toFinset, ?_, ?_⟩
  · have h1 : S.ncard = (g '' S).ncard := (Set.ncard_image_of_injOn g_inj).symm
    have h2 : (g '' S).ncard = himg_finite.toFinset.card :=
      Set.ncard_eq_toFinset_card _ himg_finite
    omega
  · intro w hw
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    have ha_A : ErdosSetA a := ha.1
    have ha_le : a ≤ N := ha.2
    constructor
    · exact canonword_mult_pos (g a)
    · calc (g a).mult ≤ (g a).apply 1 := value_ge_mult (g a)
        _ = a := g_spec a ha_A
        _ ≤ N := ha_le

-- The single-op Dirichlet weight q(s)
noncomputable def single_op_weight (s : ℝ) : ℝ :=
  ∑' (op : NTOp), ((op.mult : ℝ) ^ (-s))

-- Equiv between NTOp and Unit ⊕ ℕ for tsum decomposition
def ntopEquiv : NTOp ≃ Unit ⊕ ℕ where
  toFun | NTOp.f6 => Sum.inl () | NTOp.gk k => Sum.inr k
  invFun | Sum.inl () => NTOp.f6 | Sum.inr k => NTOp.gk k
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; rcases x with ⟨⟩ | k <;> simp

-- Helper: decompose (3·2^k)^{-s} = 3^{-s} · (2^{-s})^k
lemma ntop_gk_rpow (s : ℝ) (k : ℕ) :
    ((NTOp.gk k).mult : ℝ) ^ (-s) = (3:ℝ)^(-s) * ((2:ℝ)^(-s))^k := by
  simp only [NTOp.mult]
  have : ((3 * 2 ^ k : ℕ) : ℝ) = (3 : ℝ) * (2 : ℝ) ^ k := by push_cast; ring
  rw [this, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ↑k * -s = (-s) * ↑k from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

-- Helper: version with cast from ℕ for the NTOp.mult unfolded form
lemma gk_cast_rpow (k : ℕ) :
    ((3 * 2 ^ k : ℕ) : ℝ) ^ (-(19/20 : ℝ)) = (3:ℝ)^(-(19/20:ℝ)) * ((2:ℝ)^(-(19/20:ℝ)))^k := by
  have : ((3 * 2 ^ k : ℕ) : ℝ) = (3 : ℝ) * (2 : ℝ) ^ k := by push_cast; ring
  rw [this, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
  congr 1
  rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show ↑k * -(19/20 : ℝ) = (-(19/20:ℝ)) * ↑k from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

-- Helper: 2^{-19/20} < 1
lemma two_rpow_neg_lt_one : (2:ℝ) ^ (-(19/20 : ℝ)) < 1 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  exact inv_lt_one_of_one_lt₀ (by
    rw [Real.one_lt_rpow_iff_of_pos (by norm_num : (0:ℝ) < 2)]
    left; exact ⟨by norm_num, by norm_num⟩)

-- Helper: 2^{-19/20} ≥ 0
lemma two_rpow_neg_nonneg : 0 ≤ (2:ℝ) ^ (-(19/20 : ℝ)) :=
  Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _

-- Helper: gk series is summable (geometric series with ratio 2^{-19/20})
lemma gk_summable :
    Summable (fun k : ℕ => ((NTOp.gk k).mult : ℝ) ^ (-(19/20 : ℝ))) := by
  simp_rw [ntop_gk_rpow]
  exact (summable_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one).mul_left _

lemma single_op_summable :
    Summable (fun op : NTOp => ((op.mult : ℝ) ^ (-(19/20 : ℝ)))) := by
  rw [← Equiv.summable_iff ntopEquiv.symm]
  apply Summable.sum
  · exact summable_of_finite_support (Set.Finite.subset (Set.finite_univ) (Set.subset_univ _))
  · show Summable (fun k => ((NTOp.gk k).mult : ℝ) ^ (-(19/20 : ℝ)))
    exact gk_summable

lemma rpow_bound_2 : (2 : ℝ) ^ (-(19/20 : ℝ)) ≤ 10/19 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [inv_le_comm₀ (by positivity : 0 < (2:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 10/19)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  push_cast
  conv_lhs => rw [show (19:ℝ)/10 = ((19/10 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (19/10 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 19/10)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_3 : (3 : ℝ) ^ (-(19/20 : ℝ)) ≤ 5/14 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3)]
  rw [inv_le_comm₀ (by positivity : 0 < (3:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 5/14)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  push_cast
  conv_lhs => rw [show (14:ℝ)/5 = ((14/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (14/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 14/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_6 : (6 : ℝ) ^ (-(19/20 : ℝ)) ≤ 5/27 := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 6)]
  rw [inv_le_comm₀ (by positivity : 0 < (6:ℝ) ^ ((19:ℝ)/20)) (by positivity : (0:ℝ) < 5/27)]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 6)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  push_cast
  conv_lhs => rw [show (27:ℝ)/5 = ((27/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (27/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 27/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma rpow_bound_12 : 5/53 ≤ (12 : ℝ) ^ (-(19/20 : ℝ)) := by
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 12)]
  rw [le_inv_comm₀ (by positivity : (0:ℝ) < 5/53) (by positivity : 0 < (12:ℝ) ^ ((19:ℝ)/20))]
  simp only [inv_div]
  rw [show (19:ℝ)/20 = 19 * (20:ℝ)⁻¹ from by ring]
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 12)]
  rw [show (19:ℝ) = ((19:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [show (20:ℝ)⁻¹ = 1/(20:ℝ) from by ring]
  push_cast
  conv_rhs => rw [show (53:ℝ)/5 = ((53/5 : ℝ)^20)^((1:ℝ)/20) from by
    rw [← Real.rpow_natCast (53/5 : ℝ) 20, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 53/5)]
    norm_num]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num : (0:ℝ) ≤ 1/20)
  norm_num

lemma single_op_weight_eq :
    single_op_weight (19/20 : ℝ) =
    (6 : ℝ) ^ (-(19/20 : ℝ)) + (3 : ℝ) ^ (-(19/20 : ℝ)) / (1 - (2 : ℝ) ^ (-(19/20 : ℝ))) := by
  unfold single_op_weight
  rw [single_op_summable.tsum_eq_add_tsum_ite NTOp.f6]
  simp only [NTOp.mult]
  congr 1
  rw [← Function.Injective.tsum_eq
      (g := NTOp.gk) (by intro a b h; cases h; rfl)
      (by intro op hop
          simp only [Function.mem_support] at hop
          cases op with
          | f6 => simp at hop
          | gk k => exact ⟨k, rfl⟩)]
  simp only [reduceCtorEq, ↓reduceIte]
  simp_rw [gk_cast_rpow]
  rw [tsum_mul_left, tsum_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one]
  ring

lemma one_sub_two_rpow_pos : 0 < 1 - (2 : ℝ) ^ (-(19/20 : ℝ)) := by
  have h := rpow_bound_2; linarith

lemma q_lt_one : single_op_weight (19/20 : ℝ) < 1 := by
  rw [single_op_weight_eq]
  have h2 := rpow_bound_2
  have h3 := rpow_bound_3
  have h6 := rpow_bound_6
  have hpos := one_sub_two_rpow_pos
  have hden : (9:ℝ)/19 ≤ 1 - (2:ℝ) ^ (-(19/20 : ℝ)) := by linarith
  have hden_pos : (0:ℝ) < 9/19 := by norm_num
  calc (6:ℝ) ^ (-(19/20 : ℝ)) + (3:ℝ) ^ (-(19/20 : ℝ)) / (1 - (2:ℝ) ^ (-(19/20 : ℝ)))
      ≤ 5/27 + (5/14) / (1 - (2:ℝ) ^ (-(19/20 : ℝ))) := by
        gcongr
    _ ≤ 5/27 + (5/14) / (9/19) := by
        gcongr
    _ = 355/378 := by norm_num
    _ < 1 := by norm_num

lemma q_nonneg : 0 ≤ single_op_weight (19/20 : ℝ) := by
  unfold single_op_weight
  apply tsum_nonneg
  intro op
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

-- Equivalence: {l : List NTOp // l.length = n+1} ≃ NTOp × {l : List NTOp // l.length = n}
def listLenSuccEquiv (n : ℕ) :
    {l : List NTOp // l.length = n + 1} ≃ NTOp × {l : List NTOp // l.length = n} where
  toFun := fun ⟨l, hl⟩ =>
    match l, hl with
    | op :: rest, h => ⟨op, ⟨rest, by simp at h; exact h⟩⟩
  invFun := fun ⟨op, ⟨rest, hr⟩⟩ => ⟨op :: rest, by simp [hr]⟩
  left_inv := by
    intro ⟨l, hl⟩
    match l, hl with
    | op :: rest, h => simp
  right_inv := by
    intro ⟨op, ⟨rest, hr⟩⟩
    simp

-- {l : List NTOp // l.length = 0} is unique (only element is ⟨[], rfl⟩)
instance : Unique {l : List NTOp // l.length = 0} where
  default := ⟨[], rfl⟩
  uniq := by
    intro ⟨l, hl⟩
    simp only [Subtype.mk.injEq]
    exact List.eq_nil_of_length_eq_zero hl

lemma listLenSuccEquiv_symm_apply (n : ℕ) (op : NTOp) (rest : {l : List NTOp // l.length = n}) :
    ((listLenSuccEquiv n).symm (op, rest)).val = op :: rest.val := by
  simp [listLenSuccEquiv]

-- Summability of the ops series restricted to lists of length n
lemma ops_length_n_summable (n : ℕ) :
    Summable (fun ops : {l : List NTOp // l.length = n} =>
      ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ)))) := by
  induction n with
  | zero =>
    exact summable_of_finite_support
      (Set.Finite.subset (Set.finite_univ) (Set.subset_univ _))
  | succ n ih =>
    have heq : (fun ops : {l : List NTOp // l.length = n + 1} =>
        ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ)))) =
      (fun p : NTOp × {l : List NTOp // l.length = n} =>
        ((ntOpsMult ((listLenSuccEquiv n).symm p).val : ℝ) ^ (-(19/20 : ℝ)))) ∘
      (listLenSuccEquiv n) := by
      ext ⟨l, hl⟩
      simp [Function.comp]
    rw [heq, Equiv.summable_iff]
    suffices h : Summable (fun p : NTOp × {l : List NTOp // l.length = n} =>
        ((p.1.mult : ℝ) ^ (-(19/20 : ℝ))) * ((ntOpsMult p.2.val : ℝ) ^ (-(19/20 : ℝ)))) by
      apply h.of_nonneg_of_le
        (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      intro ⟨op, rest⟩
      rw [listLenSuccEquiv_symm_apply, ntOpsMult,
        show ((op.mult * ntOpsMult rest.val : ℕ) : ℝ) = (op.mult : ℝ) * (ntOpsMult rest.val : ℝ)
          from by push_cast; ring,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact Summable.mul_of_nonneg single_op_summable ih
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

-- Helper: sum over lists of length n equals q^n
set_option maxHeartbeats 3200000 in
lemma ops_length_n_sum (n : ℕ) :
    ∑' (ops : {l : List NTOp // l.length = n}),
      ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))) =
    single_op_weight (19/20 : ℝ) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have huniq : ∀ (x : {l : List NTOp // l.length = 0}), x = default := Unique.eq_default
    rw [tsum_eq_single default (fun b hb => absurd (huniq b) hb)]
    simp [ntOpsMult]
  | succ n ih =>
    rw [pow_succ, mul_comm, ← ih]
    have step1 : ∑' (ops : {l : List NTOp // l.length = n + 1}),
          ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))) =
        ∑' (p : NTOp × {l : List NTOp // l.length = n}),
          ((p.1.mult : ℝ) ^ (-(19/20 : ℝ))) * ((ntOpsMult p.2.val : ℝ) ^ (-(19/20 : ℝ))) := by
      have := (listLenSuccEquiv n).symm.tsum_eq
        (fun ops : {l : List NTOp // l.length = n + 1} =>
          ((ntOpsMult ops.val : ℝ) ^ (-(19/20 : ℝ))))
      rw [← this]
      congr 1
      ext ⟨op, rest⟩
      rw [listLenSuccEquiv_symm_apply, ntOpsMult,
        show ((op.mult * ntOpsMult rest.val : ℕ) : ℝ) = (op.mult : ℝ) * (ntOpsMult rest.val : ℝ)
          from by push_cast; ring,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    rw [step1]
    symm
    unfold single_op_weight
    have hf_norm : Summable (fun x : NTOp => ‖((x.mult : ℝ) ^ (-(19/20 : ℝ)))‖) := by
      have : ∀ (x : NTOp), ‖((x.mult : ℝ) ^ (-(19/20 : ℝ)))‖ =
          ((x.mult : ℝ) ^ (-(19/20 : ℝ))) :=
        fun x => Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [this]
      exact single_op_summable
    have hg_norm : Summable (fun x : {l : List NTOp // l.length = n} =>
        ‖((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ)))‖) := by
      have : ∀ (x : {l : List NTOp // l.length = n}),
          ‖((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ)))‖ =
          ((ntOpsMult x.val : ℝ) ^ (-(19/20 : ℝ))) :=
        fun x => Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      simp_rw [this]
      exact ops_length_n_summable n
    rw [tsum_mul_tsum_of_summable_norm hf_norm hg_norm]

-- Equivalence: List NTOp ≃ Σ (n : ℕ), {l : List NTOp // l.length = n}
def listLengthEquiv : (Σ (n : ℕ), {l : List NTOp // l.length = n}) ≃ List NTOp :=
  Equiv.sigmaFiberEquiv List.length

set_option maxHeartbeats 1600000 in
lemma ops_series_summable :
    Summable (fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) := by
  rw [← Equiv.summable_iff listLengthEquiv]
  show Summable ((fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) ∘ listLengthEquiv)
  have : ((fun ops : List NTOp => ((ntOpsMult ops : ℝ) ^ (-(19/20 : ℝ)))) ∘ listLengthEquiv) =
      (fun σ : Σ (n : ℕ), {l : List NTOp // l.length = n} =>
        ((ntOpsMult σ.2.val : ℝ) ^ (-(19/20 : ℝ)))) := by
    ext ⟨n, l, hl⟩
    simp [listLengthEquiv, Equiv.sigmaFiberEquiv]
  rw [this]
  rw [summable_sigma_of_nonneg (fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact ⟨fun n => ops_length_n_summable n,
    by simp_rw [ops_length_n_sum]; exact summable_geometric_of_lt_one q_nonneg q_lt_one⟩

lemma terminal_series_summable :
    Summable (fun t : ℕ => ((2 : ℝ) ^ (t : ℝ)) ^ (-(19/20 : ℝ))) := by
  -- Rewrite (2^(t:ℝ))^(-19/20) = (2^(-19/20))^t
  have h : ∀ t : ℕ, ((2 : ℝ) ^ (t : ℝ)) ^ (-(19/20 : ℝ)) = ((2:ℝ) ^ (-(19/20 : ℝ))) ^ t := by
    intro t
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [show (↑t * -(19/20 : ℝ)) = (-(19/20 : ℝ)) * ↑t from by ring]
    rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    rw [Real.rpow_natCast]
  simp_rw [h]
  exact summable_geometric_of_lt_one two_rpow_neg_nonneg two_rpow_neg_lt_one

-- Equivalence: CanonWord ≃ List NTOp × ℕ
def canonWordEquiv : CanonWord ≃ List NTOp × ℕ where
  toFun w := (w.ops, w.terminal)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 3200000 in
lemma canonword_dirichlet_summable :
    Summable (fun w : CanonWord => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) := by
  have h1 : (fun w : CanonWord => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) =
      (fun p : List NTOp × ℕ =>
        ((ntOpsMult p.1 : ℝ) ^ (-(19/20 : ℝ))) * (((2 : ℝ) ^ (p.2 : ℝ)) ^ (-(19/20 : ℝ)))) ∘
      canonWordEquiv := by
    ext w
    simp only [Function.comp, canonWordEquiv, CanonWord.mult]
    rw [show ((ntOpsMult w.ops * 2 ^ w.terminal : ℕ) : ℝ) =
        (ntOpsMult w.ops : ℝ) * ((2 : ℝ) ^ (w.terminal : ℝ)) from by
      push_cast; rw [Real.rpow_natCast]]
    exact Real.mul_rpow (Nat.cast_nonneg _) (by positivity)
  rw [h1, Equiv.summable_iff]
  exact Summable.mul_of_nonneg ops_series_summable terminal_series_summable
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => Real.rpow_nonneg (by positivity) _)

lemma canonical_dirichlet_bound :
    ∃ D : ℝ, 0 < D ∧
    ∀ (W : Finset CanonWord),
      W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) ≤ D := by
  -- Use the tsum as D (it is finite by canonword_dirichlet_summable)
  have hsumm := canonword_dirichlet_summable
  refine ⟨∑' (w : CanonWord), ((w.mult : ℝ) ^ (-(19/20 : ℝ))), ?_, fun W => ?_⟩
  · have hterm : (0 : ℝ) < ((⟨[], 0⟩ : CanonWord).mult : ℝ) ^ (-(19/20 : ℝ)) := by
      have : (⟨[], 0⟩ : CanonWord).mult = 1 := by simp [CanonWord.mult, ntOpsMult]
      rw [this]; simp
    exact lt_of_lt_of_le hterm (Summable.le_tsum hsumm ⟨[], 0⟩
      (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · exact Summable.sum_le_tsum W (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsumm

lemma erdos_set_sublinear_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 0 < N →
      (Set.ncard (setOf ErdosSetA ∩ Set.Iic N) : ℝ) ≤ C * (N : ℝ) ^ (19/20 : ℝ) := by
  obtain ⟨D, hDpos, hDbound⟩ := canonical_dirichlet_bound
  refine ⟨D, hDpos, fun N hN => ?_⟩
  obtain ⟨W, hcard, hW⟩ := erdos_injection_canonical N
  have hrankin := rankin_trick W CanonWord.mult N (19/20 : ℝ) (by norm_num) hN
    (fun w hw => hW w hw)
  have hsum := hDbound W
  have h1 : (Set.ncard (setOf ErdosSetA ∩ Set.Iic N) : ℝ) ≤ (W.card : ℝ) :=
    Nat.cast_le.mpr hcard
  have h2 : (N : ℝ) ^ (19/20 : ℝ) * W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) ≤
      (N : ℝ) ^ (19/20 : ℝ) * D :=
    mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  calc (Set.ncard (setOf ErdosSetA ∩ Set.Iic N) : ℝ)
      ≤ W.card := h1
    _ ≤ (N : ℝ) ^ (19/20 : ℝ) * W.sum (fun w => ((w.mult : ℝ) ^ (-(19/20 : ℝ)))) := hrankin
    _ ≤ (N : ℝ) ^ (19/20 : ℝ) * D := h2
    _ = D * (N : ℝ) ^ (19/20 : ℝ) := mul_comm _ _

lemma sublinear_bound_implies_density_zero (S : Set ℕ) (C : ℝ) (α : ℝ)
    (hC : 0 < C) (hα : α < 1)
    (hbound : ∀ N : ℕ, 0 < N → (Set.ncard (S ∩ Set.Iic N) : ℝ) ≤ C * (N : ℝ) ^ α) :
    lowerDensity S = 0 := by
  unfold lowerDensity
  have htend : Filter.Tendsto
      (fun N : ℕ => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)) Filter.atTop (nhds 0) := by
    apply squeeze_zero (f := fun N => (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ))
      (g := fun N : ℕ => C * (N : ℝ) ^ (α - 1))
    · intro N
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro N
      by_cases hN : N = 0
      · subst hN
        simp only [Nat.cast_zero, div_zero]
        apply mul_nonneg (le_of_lt hC)
        exact Real.rpow_nonneg (le_refl 0) _
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
        have hNcast : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
        have hbound' := hbound N hNpos
        calc (Set.ncard (S ∩ Set.Iic N) : ℝ) / (N : ℝ)
            ≤ (C * (N : ℝ) ^ α) / (N : ℝ) := by
              apply div_le_div_of_nonneg_right hbound' (le_of_lt hNcast)
          _ = C * ((N : ℝ) ^ α / (N : ℝ)) := by ring
          _ = C * (N : ℝ) ^ (α - 1) := by
              rw [Real.rpow_sub_one (ne_of_gt hNcast)]
    · have h1α : 0 < 1 - α := by linarith
      have hαeq : α - 1 = -(1 - α) := by ring
      simp_rw [hαeq]
      rw [show (0 : ℝ) = C * 0 from by ring]
      apply Filter.Tendsto.const_mul
      exact (tendsto_rpow_neg_atTop h1α).comp tendsto_natCast_atTop_atTop
  exact htend.liminf_eq

theorem lowerDensity_eq_zero : lowerDensity (setOf ErdosSetA) = 0 := by
  obtain ⟨C, hC, hbound⟩ := erdos_set_sublinear_bound
  exact sublinear_bound_implies_density_zero (setOf ErdosSetA) C (19/20 : ℝ)
    hC (by norm_num) hbound

/-- **Erdős Problem 1134.** The conjecture is **false**: Lagarias [La16] reports
that Erdős asked in 1972 whether `A` (the smallest subset of `ℕ` containing `1` and
closed under `x ↦ 2x+1`, `x ↦ 3x+1`, `x ↦ 6x+1`) has positive lower density. The
answer is no — in fact `d(A) = 0`. -/
theorem erdos_1134 : ¬ (0 < lowerDensity (setOf ErdosSetA)) := by
  rw [lowerDensity_eq_zero]
  exact lt_irrefl 0

#print axioms erdos_1134
-- 'Erdos1134.erdos_1134' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1134
