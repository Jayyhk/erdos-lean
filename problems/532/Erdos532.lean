import Mathlib

namespace Erdos532

open Hindman Stream' Finset

private def lift (a : Stream' ℕ+) : Stream' ℕ := fun i => (a.get i : ℕ)

private lemma fs_lift_of_fs (a : Stream' ℕ+) (m : ℕ+) (hm : m ∈ FS a) :
    ((m : ℕ+) : ℕ) ∈ FS (lift a) := by
  induction hm with
  | head' a' => exact FS.head (lift a')
  | tail' a' m _ ih => exact FS.tail (lift a') ((m : ℕ+) : ℕ) ih
  | cons' a' m _ ih =>
    rw [show ((a'.head + m : ℕ+) : ℕ) = (lift a').head + ((m : ℕ+) : ℕ) from PNat.add_coe _ _]
    exact FS.cons (lift a') ((m : ℕ+) : ℕ) ih

private lemma fs_of_fs_lift_aux : ∀ (b : Stream' ℕ) (n : ℕ), n ∈ FS b →
    ∀ (a : Stream' ℕ+), b = lift a → ∃ m : ℕ+, m ∈ FS a ∧ ((m : ℕ+) : ℕ) = n := by
  intro b n hn
  induction hn with
  | head' b =>
    intro a hba
    refine ⟨a.head, FS.head _, ?_⟩
    rw [hba]; rfl
  | tail' b m _ ih =>
    intro a hba
    have h_tail : b.tail = lift a.tail := by rw [hba]; rfl
    obtain ⟨m', hm'_in, hm'_eq⟩ := ih a.tail h_tail
    exact ⟨m', FS.tail a m' hm'_in, hm'_eq⟩
  | cons' b m _ ih =>
    intro a hba
    have h_tail : b.tail = lift a.tail := by rw [hba]; rfl
    obtain ⟨m', hm'_in, hm'_eq⟩ := ih a.tail h_tail
    refine ⟨a.head + m', FS.cons a m' hm'_in, ?_⟩
    rw [PNat.add_coe, hm'_eq, hba]; rfl

private lemma fs_of_fs_lift {a : Stream' ℕ+} (n : ℕ) (hn : n ∈ FS (lift a)) :
    ∃ m : ℕ+, m ∈ FS a ∧ ((m : ℕ+) : ℕ) = n :=
  fs_of_fs_lift_aux _ _ hn a rfl

/-- Finite-sum membership in `FS`: this is the additive version of `Hindman.FP.finset_prod`. -/
private lemma fs_finset_sum (a : Stream' ℕ) (s : Finset ℕ) (hs : s.Nonempty) :
    (∑ i ∈ s, a.get i) ∈ FS a :=
  FS.finset_sum a s hs

/-- **Erdős Problem 532** (special case of Hindman's theorem with 2 colours).
If `ℕ` is 2-coloured then there is some infinite `A ⊆ ℕ` such that all finite subset
sums `∑_{n ∈ S} n` (as `S` ranges over the non-empty finite subsets of `A`) lie in a
single colour class. Proved by Hindman (1974) for any number of colours; here we invoke
`Hindman.exists_FS_of_finite_cover` from Mathlib over `ℕ+` and bridge to the literal
"infinite set" form via dyadic-block sums. -/
theorem erdos_532 (c : ℕ → Fin 2) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ k : Fin 2,
      ∀ S : Finset ℕ, S.Nonempty → ↑S ⊆ A → c (∑ n ∈ S, n) = k := by
  let c' : ℕ+ → Fin 2 := fun n => c n.val
  let scov : Set (Set ℕ+) := {c' ⁻¹' {0}, c' ⁻¹' {1}}
  have scov_fin : scov.Finite := (Set.finite_singleton _).insert _
  have hcov : (⊤ : Set ℕ+) ⊆ ⋃₀ scov := by
    intro n _
    match h : c' n with
    | 0 => exact ⟨c' ⁻¹' {0}, Or.inl rfl, h⟩
    | 1 => exact ⟨c' ⁻¹' {1}, Or.inr rfl, h⟩
  obtain ⟨T, hT_in, a, ha⟩ := exists_FS_of_finite_cover scov scov_fin hcov
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, T = c' ⁻¹' {k} := by
    rcases hT_in with rfl | hT
    · exact ⟨0, rfl⟩
    · simp at hT; subst hT; exact ⟨1, rfl⟩
  subst hk
  let block : ℕ → Finset ℕ := fun i => Finset.Ico (2^i - 1) (2^(i+1) - 1)
  have block_card : ∀ i, (block i).card = 2^i := fun i => by
    show (Finset.Ico _ _).card = _
    rw [Nat.card_Ico]
    have h1 : 1 ≤ 2^i := Nat.one_le_two_pow
    have h2 : 2^(i+1) = 2 * 2^i := by ring
    omega
  have block_nonempty : ∀ i, (block i).Nonempty := fun i => by
    rw [← Finset.card_pos, block_card]; positivity
  have block_disj : ∀ {i j}, i < j → Disjoint (block i) (block j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [block, Finset.mem_Ico] at hxi hxj
    have : 2^(i+1) ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hij
    omega
  let bsum : ℕ → ℕ := fun i => ∑ j ∈ block i, ((a.get j : ℕ+) : ℕ)
  have bsum_ge : ∀ i, 2^i ≤ bsum i := fun i => by
    calc 2^i = (block i).card := (block_card i).symm
      _ = ∑ _ ∈ block i, 1 := by simp
      _ ≤ bsum i := Finset.sum_le_sum (fun j _ => (a.get j).property)
  have color : ∀ n ∈ FS (lift a), c n = k := by
    intro n hn
    obtain ⟨m, hm_in, hm_eq⟩ := fs_of_fs_lift n hn
    have := ha hm_in
    show c n = k
    rw [← hm_eq]; exact this
  refine ⟨Set.range bsum, ?_, k, ?_⟩
  · apply Set.infinite_of_not_bddAbove
    rintro ⟨M, hM⟩
    have hi : M < 2^(M+1) := by
      have := @Nat.lt_two_pow_self (M+1)
      omega
    have h1 : bsum (M+1) ≤ M := hM ⟨M+1, rfl⟩
    have h2 : 2^(M+1) ≤ M := le_trans (bsum_ge (M+1)) h1
    omega
  · intro S hS_ne hS_sub
    have h_in : ∀ s ∈ S, ∃ i, bsum i = s := fun s hs => hS_sub hs
    choose pick pick_eq using h_in
    have pick_inj : ∀ s₁ (h₁ : s₁ ∈ S) s₂ (h₂ : s₂ ∈ S), pick s₁ h₁ = pick s₂ h₂ → s₁ = s₂ := by
      intro s₁ h₁ s₂ h₂ heq
      rw [← pick_eq s₁ h₁, ← pick_eq s₂ h₂, heq]
    let K : Finset ℕ := S.attach.image (fun ⟨s, hs⟩ => pick s hs)
    have blocks_disj : ((K : Set ℕ).PairwiseDisjoint block) := by
      intro i _ j _ hij
      rcases lt_trichotomy i j with h | h | h
      · exact block_disj h
      · exact absurd h hij
      · exact (block_disj h).symm
    have sum_bij : (∑ s ∈ S, s) = ∑ i ∈ K, bsum i := by
      apply Finset.sum_bij (fun s hs => pick s hs)
      · intro s hs
        show pick s hs ∈ S.attach.image _
        exact Finset.mem_image.mpr ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
      · intro s₁ h₁ s₂ h₂ heq
        exact pick_inj s₁ h₁ s₂ h₂ heq
      · intro k hk
        obtain ⟨⟨s, hs⟩, _, rfl⟩ := Finset.mem_image.mp hk
        exact ⟨s, hs, rfl⟩
      · intro s hs
        exact (pick_eq s hs).symm
    have sum_biUnion : ∑ i ∈ K, bsum i = ∑ j ∈ K.biUnion block, ((a.get j : ℕ+) : ℕ) := by
      rw [Finset.sum_biUnion blocks_disj]
    have biUnion_ne : (K.biUnion block).Nonempty := by
      obtain ⟨s, hs⟩ := hS_ne
      refine ⟨2^(pick s hs) - 1, ?_⟩
      rw [Finset.mem_biUnion]
      refine ⟨pick s hs, ?_, ?_⟩
      · show pick s hs ∈ S.attach.image _
        rw [Finset.mem_image]
        exact ⟨⟨s, hs⟩, Finset.mem_attach _ _, rfl⟩
      · show _ ∈ Finset.Ico _ _
        rw [Finset.mem_Ico]
        have h1 : 1 ≤ 2^(pick s hs) := Nat.one_le_two_pow
        refine ⟨by omega, ?_⟩
        have h2 : 2^(pick s hs) < 2^(pick s hs + 1) :=
          Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)
        omega
    have biUnion_in_FS : ∑ j ∈ K.biUnion block, ((a.get j : ℕ+) : ℕ) ∈ FS (lift a) := by
      show ∑ j ∈ K.biUnion block, (lift a).get j ∈ FS (lift a)
      exact fs_finset_sum (lift a) (K.biUnion block) biUnion_ne
    rw [sum_bij, sum_biUnion]
    exact color _ biUnion_in_FS

#print axioms erdos_532
-- 'Erdos532.erdos_532' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos532
