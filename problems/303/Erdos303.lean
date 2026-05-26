import Mathlib
import Aesop
set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace Erdos303


theorem get_finite_natural_coloring_from_integer_coloring (𝓒 : ℤ → ℤ)
  (h_finite : (Set.range 𝓒).Finite):
  ∃ (χ : ℕ → ℤ), (Set.range χ).Finite ∧ (∀ (n : ℕ), χ n = 𝓒 (n : ℤ)) := by
  use fun (n : ℕ) => 𝓒 (n : ℤ)
  constructor
  ·
    have h₁ : Set.range (fun (n : ℕ) => 𝓒 (n : ℤ)) ⊆ Set.range 𝓒 := by
      intro x hx
      rcases hx with ⟨n, rfl⟩
      exact ⟨(n : ℤ), by simp⟩
    exact Set.Finite.subset h_finite h₁
  ·
    intro n
    <;> rfl

lemma round1_h_main (a b c : ℤ)
  (ha_ne_zero : a ≠ 0)
  (hb_ne_zero : b ≠ 0)
  (hc_ne_zero : c ≠ 0)
  (h_a_ne_b : a ≠ b)
  (h_b_ne_c : b ≠ c)
  (h_a_ne_c : a ≠ c):
  [a, b, c, 0].Nodup := by
  simp [List.nodup_cons, ha_ne_zero, hb_ne_zero, hc_ne_zero, h_a_ne_b, h_b_ne_c, h_a_ne_c]
  <;>
  tauto

theorem distinct_nonzero_integers_form_nodup_list_with_zero (a b c : ℤ)
  (ha_ne_zero : a ≠ 0)
  (hb_ne_zero : b ≠ 0)
  (hc_ne_zero : c ≠ 0)
  (h_a_ne_b : a ≠ b)
  (h_b_ne_c : b ≠ c)
  (h_a_ne_c : a ≠ c):
  [a, b, c, 0].Nodup := by
  exact round1_h_main a b c ha_ne_zero hb_ne_zero hc_ne_zero h_a_ne_b h_b_ne_c h_a_ne_c

lemma round1_product_k_y_z_is_nonzero (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * y * z : ℤ) ≠ 0 := by
  have h1 : 0 < k := by linarith
  have h2 : 0 < y := by linarith
  have h3 : 0 < z := by linarith
  have h4 : 0 < k * y * z := by positivity
  have h5 : (k * y * z : ℤ) > 0 := by exact_mod_cast h4
  have h6 : (k * y * z : ℤ) ≠ 0 := by linarith
  exact h6

lemma round1_div_y_eq_kz (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  ((k * y * z : ℤ) / (y : ℤ)) = (k * z : ℤ) := by
  have hy' : (y : ℤ) ≠ 0 := by
    have hhy : (y : ℤ) > 0 := by exact_mod_cast hy
    linarith
  have h_eq : ((k * y * z : ℤ)) = ((k * z : ℤ)) * (y : ℤ) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring
  rw [h_eq]
  field_simp [hy']
  <;> ring

lemma round1_div_k_eq_yz (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  ((k * y * z : ℤ) / (k : ℤ)) = (y * z : ℤ) := by
  have hk' : (k : ℤ) ≠ 0 := by
    have hhk : (k : ℤ) > 0 := by exact_mod_cast hk
    linarith
  have h_eq : ((k * y * z : ℤ)) = (k : ℤ) * (y * z : ℤ) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring
  rw [h_eq]
  field_simp [hk']
  <;> ring

lemma round1_div_z_eq_ky (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  ((k * y * z : ℤ) / (z : ℤ)) = (k * y : ℤ) := by
  have hz' : (z : ℤ) ≠ 0 := by
    have hhz : (z : ℤ) > 0 := by exact_mod_cast hz
    linarith
  have h_eq : ((k * y * z : ℤ)) = (z : ℤ) * (k * y : ℤ) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
    <;> ring
  rw [h_eq]
  field_simp [hz']
  <;> ring

theorem product_k_y_z_is_nonzero (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * y * z : ℤ) ≠ 0 := by
  exact round1_product_k_y_z_is_nonzero k y z hk hy hz

lemma round1_product_pos (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * z * (y + z) : ℤ) ≠ 0 := by
  have h1 : k > 0 := by linarith
  have h2 : z > 0 := by linarith
  have h3 : y + z > 0 := by linarith
  have h4 : (k * z * (y + z)) > 0 := by positivity
  have h5 : ((k * z * (y + z) : ℤ)) > 0 := by exact_mod_cast h4
  have h6 : ((k * z * (y + z) : ℤ)) ≠ 0 := by linarith
  exact h6

theorem product_k_z_y_add_z_is_nonzero (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * z * (y + z) : ℤ) ≠ 0 := by
  exact round1_product_pos k y z hk hy hz

lemma round1_h_main_601014 (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * y * (y + z) : ℤ) ≠ 0 := by
  have h1 : k ≠ 0 := by
    omega
  have h2 : y ≠ 0 := by
    omega
  have h3 : y + z ≠ 0 := by
    omega
  have h4 : k * y * (y + z) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero h1 h2
    · exact h3
  exact_mod_cast h4

theorem product_k_y_y_add_z_is_nonzero (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1):
  (k * y * (y + z) : ℤ) ≠ 0 := by
  exact round1_h_main_601014 k y z hk hy hz

theorem product_k_y_z_ne_product_k_z_y_add_z (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * y * z : ℤ) ≠ (k * z * (y + z) : ℤ) := by
  intro h
  have hk' : (k : ℤ) ≠ 0 := by
    have h₁ : (k : ℤ) > 0 := by exact_mod_cast hk
    linarith
  have h₁ : ((y : ℤ) * (z : ℤ)) = ((z : ℤ) * ((y : ℤ) + (z : ℤ))) := by
    apply mul_left_cancel₀ hk'
    simpa [mul_assoc] using h
  have hz' : (z : ℤ) ≠ 0 := by
    have h₂ : (z : ℤ) > 0 := by exact_mod_cast hz
    linarith
  have h₂ : (y : ℤ) = ((y : ℤ) + (z : ℤ)) := by
    apply mul_left_cancel₀ hz'
    simpa [mul_comm] using h₁
  have h₃ : (z : ℤ) = 0 := by linarith
  have h₄ : (z : ℤ) > 0 := by exact_mod_cast hz
  linarith

lemma round1_h_main_77db7e (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) := by
  by_contra h
  have h₁ : (k : ℤ) ≠ 0 := by
    have h₂ : (k : ℤ) ≥ 1 := by exact_mod_cast hk
    linarith
  have h₃ : ((z : ℤ) * ((y : ℤ) + (z : ℤ))) = ((y : ℤ) * ((y : ℤ) + (z : ℤ))) := by
    apply mul_left_cancel₀ h₁
    simpa [mul_assoc] using h
  have h₄ : (y : ℤ) + (z : ℤ) > 0 := by
    have h₅ : (y : ℤ) ≥ 1 := by exact_mod_cast hy
    have h₆ : (z : ℤ) ≥ 1 := by exact_mod_cast hz
    linarith
  have h₅ : (y : ℤ) + (z : ℤ) ≠ 0 := by linarith
  have h₆ : (z : ℤ) = (y : ℤ) := by
    apply mul_right_cancel₀ h₅
    linarith
  have h₇ : z = y := by exact_mod_cast h₆
  exact hne h₇.symm

theorem product_k_z_y_add_z_ne_product_k_y_y_add_z (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) := by
  exact round1_h_main_77db7e k y z hk hy hz hne

lemma round1_main (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) := by
  intro h
  have h1 : (k : ℤ) > 0 := by exact_mod_cast (by linarith)
  have h2 : (y : ℤ) > 0 := by exact_mod_cast (by linarith)
  have h3 : (k : ℤ) * (y : ℤ) > 0 := mul_pos h1 h2
  have h4 : ((k : ℤ) * (y : ℤ)) * ((z : ℤ)) = ((k : ℤ) * (y : ℤ)) * (((y : ℤ) + (z : ℤ))) := by
    exact_mod_cast h
  have h5 : (z : ℤ) = (y : ℤ) + (z : ℤ) := by
    apply mul_left_cancel₀ (show (k : ℤ) * (y : ℤ) ≠ 0 by positivity)
    exact h4
  have h6 : (0 : ℤ) = (y : ℤ) := by linarith
  have h7 : (y : ℤ) > 0 := h2
  linarith

theorem product_k_y_z_ne_product_k_y_y_add_z (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) := by
  exact round1_main k y z hk hy hz hne

theorem reciprocal_relation_of_parametric_products (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (h1 : (k * y * z : ℤ) ≠ 0)
  (h2 : (k * z * (y + z) : ℤ) ≠ 0)
  (h3 : (k * y * (y + z) : ℤ) ≠ 0):
  (1 / ((k * y * z : ℤ) : ℝ)) = (1 / ((k * z * (y + z) : ℤ) : ℝ)) + (1 / ((k * y * (y + z) : ℤ) : ℝ)) := by
  have hk' : (k : ℝ) > 0 := by exact_mod_cast (show 0 < k from by linarith)
  have hy' : (y : ℝ) > 0 := by exact_mod_cast (show 0 < y from by linarith)
  have hz' : (z : ℝ) > 0 := by exact_mod_cast (show 0 < z from by linarith)
  have h4 : (y : ℝ) + (z : ℝ) > 0 := by linarith
  have h_main : (1 : ℝ) / ((k : ℝ) * (y : ℝ) * (z : ℝ)) =
    (1 : ℝ) / ((k : ℝ) * (z : ℝ) * ((y : ℝ) + (z : ℝ))) + (1 : ℝ) / ((k : ℝ) * (y : ℝ) * ((y : ℝ) + (z : ℝ))) := by
    field_simp
    <;> ring
  have h1' : (( (k * y * z : ℤ) : ℝ)) = (k : ℝ) * (y : ℝ) * (z : ℝ) := by
    simp [mul_assoc]
    <;> ring
  have h2' : (( (k * z * (y + z) : ℤ) : ℝ)) = (k : ℝ) * (z : ℝ) * ((y : ℝ) + (z : ℝ)) := by
    simp [mul_assoc]
    <;> ring
  have h3' : (( (k * y * (y + z) : ℤ) : ℝ)) = (k : ℝ) * (y : ℝ) * ((y : ℝ) + (z : ℝ)) := by
    simp [mul_assoc]
    <;> ring
  rw [h1', h2', h3']
  exact h_main

theorem C_colors_are_equal_from_monochromatic_chi (𝓒 : ℤ → ℤ)
  (χ : ℕ → ℤ)
  (h_χ : ∀ (n : ℕ), χ n = 𝓒 (n : ℤ))
  (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (h_monochromatic : χ (k * y * z) = χ (k * z * (y + z)) ∧ χ (k * z * (y + z)) = χ (k * y * (y + z))):
  𝓒 ((k * y * z : ℕ) : ℤ) = 𝓒 ((k * z * (y + z) : ℕ) : ℤ) ∧
  𝓒 ((k * z * (y + z) : ℕ) : ℤ) = 𝓒 ((k * y * (y + z) : ℕ) : ℤ) := by
  have h1 : χ (k * y * z) = χ (k * z * (y + z)) := h_monochromatic.1
  have h2 : χ (k * z * (y + z)) = χ (k * y * (y + z)) := h_monochromatic.2
  have h1' : χ (k * y * z) = 𝓒 ((k * y * z : ℕ) : ℤ) := by simpa using h_χ (k * y * z)
  have h2' : χ (k * z * (y + z)) = 𝓒 ((k * z * (y + z) : ℕ) : ℤ) := by simpa using h_χ (k * z * (y + z))
  have h3' : χ (k * y * (y + z)) = 𝓒 ((k * y * (y + z) : ℕ) : ℤ) := by simpa using h_χ (k * y * (y + z))
  have h_main1 : 𝓒 ((k * y * z : ℕ) : ℤ) = 𝓒 ((k * z * (y + z) : ℕ) : ℤ) := by
    linarith [h1, h1', h2']
  have h_main2 : 𝓒 ((k * z * (y + z) : ℕ) : ℤ) = 𝓒 ((k * y * (y + z) : ℕ) : ℤ) := by
    linarith [h2, h2', h3']
  exact ⟨h_main1, h_main2⟩

lemma round1_h4 (f : ℤ → ℤ)
  (x y z v : ℤ)
  (h1 : f x = v)
  (h2 : f y = v)
  (h3 : f z = v):
  f '' {x, y, z} ⊆ {v} := by
  intro w hw
  rcases hw with ⟨u, hu, rfl⟩
  have h5 : u = x ∨ u = y ∨ u = z := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    tauto
  rcases h5 with (rfl | rfl | rfl)
  ·
    simp [h1]
  ·
    simp [h2]
  ·
    simp [h3]

lemma round1_h5 (f : ℤ → ℤ)
  (x y z v : ℤ)
  (h1 : f x = v):
  {v} ⊆ f '' {x, y, z} := by
  intro w hw
  have hw' : w = v := by simpa using hw
  rw [hw']
  have h6 : x ∈ ({x, y, z} : Set ℤ) := by simp
  have h7 : f x ∈ f '' ({x, y, z} : Set ℤ) := ⟨x, h6, rfl⟩
  simpa [h1] using h7

theorem image_of_three_integers_with_same_color_is_singleton_set (f : ℤ → ℤ)
  (x y z v : ℤ)
  (h1 : f x = v)
  (h2 : f y = v)
  (h3 : f z = v):
  f '' {x, y, z} = {v} := by
  have h4 : f '' {x, y, z} ⊆ {v} := by
    exact round1_h4 f x y z v h1 h2 h3
  have h5 : {v} ⊆ f '' {x, y, z} := by
    exact round1_h5 f x y z v h1
  have h6 : f '' {x, y, z} = {v} := by
    apply Set.Subset.antisymm h4 h5
  exact h6

lemma round1_a_singleton_set_is_subsingleton (v : ℤ)
  (s : Set ℤ)
  (h : s = {v}):
  s.Subsingleton := by
  rw [h]
  <;> simp [Set.subsingleton_singleton]
  <;> tauto

theorem a_singleton_set_is_subsingleton (v : ℤ)
  (s : Set ℤ)
  (h : s = {v}):
  s.Subsingleton := by
  trace_state
  <;> simp_all [Set.Subsingleton]
  <;> aesop

lemma lemma_factorial_gt_self (S : ℕ)
  (hS : S ≥ 4):
  S < Nat.factorial S := by
  have h_main : ∀ n : ℕ, n ≥ 4 → n < Nat.factorial n := by
    intro n hn
    induction' hn with n hn IH
    ·
      norm_num [Nat.factorial]
    ·
      have h_n_ge_4 : n ≥ 4 := by exact hn
      have h1 : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
        simp [Nat.factorial]
      have h2 : n < Nat.factorial n := IH
      have h3 : Nat.factorial n ≥ n + 1 := by linarith
      have h4 : n + 1 > 1 := by
        omega
      have h5 : (n + 1) * Nat.factorial n ≥ (n + 1) * (n + 1) := by
        exact Nat.mul_le_mul_left (n + 1) h3
      have h6 : (n + 1) * (n + 1) > n + 1 := by
        have h7 : n + 1 > 1 := h4
        have h8 : (n + 1) * (n + 1) > 1 * (n + 1) := Nat.mul_lt_mul_of_pos_right h7 (by omega)
        simpa [mul_one] using h8
      have h9 : (n + 1) * Nat.factorial n > n + 1 := by
        calc
          (n + 1) * Nat.factorial n ≥ (n + 1) * (n + 1) := h5
          _ > n + 1 := h6
      rw [h1]
      exact h9
  exact h_main S hS

lemma round1_h_main_bdb966 (S : ℕ)
  (hS : S ≥ 4):
  ∀ (k : ℕ),
    (1 ≤ k ∧ k ≤ S) →
    (k ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := by
  intro k hk
  have h1 : 1 ≤ k := hk.1
  have h2 : k ≤ S := hk.2
  have h3 : 0 < k := by linarith
  have h4 : k ∣ Nat.factorial S := Nat.dvd_factorial h3 h2
  have h5 : S < Nat.factorial S := lemma_factorial_gt_self S hS
  exact ⟨h4, h5⟩

theorem lemma_factorial_divides_and_lower_bound (S : ℕ)
  (hS : S ≥ 4):
  ∀ (k : ℕ),
    (1 ≤ k ∧ k ≤ S) →
    (k ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := by
  exact round1_h_main_bdb966 S hS

lemma h_main (χ : ℕ → ℤ)
  (S : ℕ)
  (C : Set ℤ)
  (hC_eq_range_χ : C = Set.range χ):
  let φ : ℕ → ℤ := fun (k : ℕ) => χ (Nat.factorial S / k)
  ∀ (n : ℕ), φ n ∈ C := by
  dsimp only
  intro n
  have h1 : (χ (Nat.factorial S / n)) ∈ Set.range χ := by
    exact ⟨Nat.factorial S / n, rfl⟩
  have h2 : (χ (Nat.factorial S / n)) ∈ C := by
    rw [hC_eq_range_χ]
    exact h1
  simpa using h2

theorem round1_h_main_766153 (χ : ℕ → ℤ)
  (S : ℕ)
  (C : Set ℤ)
  (hC_eq_range_χ : C = Set.range χ):
  let φ : ℕ → ℤ := fun (k : ℕ) => χ (Nat.factorial S / k)
  ∀ (n : ℕ), φ n ∈ C := by
  dsimp only
  intro n
  have h1 : (χ (Nat.factorial S / n)) ∈ Set.range χ := by
    exact ⟨Nat.factorial S / n, rfl⟩
  have h2 : (χ (Nat.factorial S / n)) ∈ C := by
    rw [hC_eq_range_χ]
    exact h1
  simpa using h2

theorem lemma_aux_coloring_range_subset_original_range (χ : ℕ → ℤ)
  (S : ℕ)
  (C : Set ℤ)
  (hC_eq_range_χ : C = Set.range χ):
  let φ : ℕ → ℤ := fun (k : ℕ) => χ (Nat.factorial S / k)
  ∀ (n : ℕ), φ n ∈ C := by
  have h_main : (let φ : ℕ → ℤ := fun (k : ℕ) => χ (Nat.factorial S / k)
    ∀ (n : ℕ), φ n ∈ C) := round1_h_main_766153 χ S C hC_eq_range_χ
  exact h_main

lemma round1_h_main_7475fb (u v S N : ℕ)
  (h1 : u + v ≤ S)
  (h2 : S < N):
  u + v < N := by
  calc
    u + v ≤ S := h1
    _ < N := h2

theorem lemma_inequality_transitivity_sum_lt_N (u v S N : ℕ)
  (h1 : u + v ≤ S)
  (h2 : S < N):
  u + v < N := by
  exact round1_h_main_7475fb u v S N h1 h2

lemma round1_h_v_le_S (u v S : ℕ)
  (hu_ge_1 : 1 ≤ u)
  (hv_ge_1 : 1 ≤ v)
  (h_u_lt_v : u < v)
  (h_sum_le_S : u + v ≤ S):
  v ≤ S := by
  have h1 : v ≤ u + v := by
    omega
  have h2 : v ≤ S := by
    omega
  exact h2

lemma round1_h_main_3d6c5c (c : ℕ → Fin 2)
  (h : ∃ S : ℕ, ∀ n > S, c n = 0):
  ∃ (a b c' : ℕ), (1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c') ∧ (a ≠ b ∧ a ≠ c' ∧ b ≠ c') ∧ ((a : ℚ) * (b : ℚ) + (a : ℚ) * (c' : ℚ) = (b : ℚ) * (c' : ℚ)) ∧ (c a = c b ∧ c b = c c') := by
  rcases h with ⟨S, hS⟩
  have h_main : ∃ (m : ℕ), m > 0 ∧ (S < 2 * m) ∧ (S < 3 * m) ∧ (S < 6 * m) := by
    refine' ⟨S + 1, by omega, by omega, by omega, by omega⟩
  rcases h_main with ⟨m, hm_pos, h1, h2, h3⟩
  let a : ℕ := 2 * m
  let b : ℕ := 3 * m
  let c' : ℕ := 6 * m
  have ha_gt_S : a > S := h1
  have hb_gt_S : b > S := h2
  have hc'_gt_S : c' > S := h3
  have hca : c a = 0 := hS a ha_gt_S
  have hcb : c b = 0 := hS b hb_gt_S
  have hcc' : c c' = 0 := hS c' hc'_gt_S
  have h4 : c a = c b := by
    rw [hca, hcb]
  have h5 : c b = c c' := by
    rw [hcb, hcc']
  have h6 : (a : ℚ) * (b : ℚ) + (a : ℚ) * (c' : ℚ) = (b : ℚ) * (c' : ℚ) := by
    have h61 : (a : ℚ) = (2 * m : ℚ) := by norm_cast
    have h62 : (b : ℚ) = (3 * m : ℚ) := by norm_cast
    have h63 : (c' : ℚ) = (6 * m : ℚ) := by norm_cast
    rw [h61, h62, h63]
    <;> ring
  have h7 : 1 ≤ a := by
    have h71 : m > 0 := hm_pos
    have h72 : 1 ≤ 2 * m := by omega
    exact_mod_cast h72
  have h8 : 1 ≤ b := by
    have h81 : m > 0 := hm_pos
    have h82 : 1 ≤ 3 * m := by omega
    exact_mod_cast h82
  have h9 : 1 ≤ c' := by
    have h91 : m > 0 := hm_pos
    have h92 : 1 ≤ 6 * m := by omega
    exact_mod_cast h92
  have h10 : a ≠ b := by
    have h101 : m > 0 := hm_pos
    omega
  have h11 : a ≠ c' := by
    have h111 : m > 0 := hm_pos
    omega
  have h12 : b ≠ c' := by
    have h121 : m > 0 := hm_pos
    omega
  exact ⟨a, b, c', ⟨h7, h8, h9⟩, ⟨h10, h11, h12⟩, h6, ⟨h4, h5⟩⟩

theorem lemma_v_le_S_from_sum_le_S_and_u_lt_v (u v S : ℕ)
  (hu_ge_1 : 1 ≤ u)
  (hv_ge_1 : 1 ≤ v)
  (h_u_lt_v : u < v)
  (h_sum_le_S : u + v ≤ S):
  v ≤ S := by
  exact?

lemma round1_h1 (u v : ℕ)
  (hu_ge_1 : 1 ≤ u)
  (hv_ge_1 : 1 ≤ v):
  1 ≤ u + v := by
  linarith

lemma round1_h2 (u v : ℕ)
  (hu_ge_1 : 1 ≤ u)
  (hv_ge_1 : 1 ≤ v):
  u * v > 0 := by
  have h₁ : u > 0 := by linarith
  have h₂ : v > 0 := by linarith
  exact mul_pos h₁ h₂

lemma round1_h_main_8dac98 (u : ℕ)
  (hu_ge_1 : 1 ≤ u):
  (1 : ℚ) / (u : ℚ) = (1 : ℚ) / ((u * (u + 1) : ℕ) : ℚ) + (1 : ℚ) / ((u + 1 : ℕ) : ℚ) := by
  have h₁ : (u : ℚ) ≥ 1 := by exact_mod_cast hu_ge_1
  have h₂ : (u : ℚ) > 0 := by linarith
  have h₃ : ((u + 1 : ℕ) : ℚ) > 0 := by positivity
  have h₄ : (((u * (u + 1) : ℕ) : ℚ)) > 0 := by positivity
  field_simp [mul_add, mul_comm]
  <;> ring_nf <;> field_simp <;> ring

lemma round1_h_eq (k : ℤ)
  (hk : k ≠ 0):
  (1 : ℚ) / ((2 * k : ℤ) : ℚ) = (1 : ℚ) / ((6 * k : ℤ) : ℚ) + (1 : ℚ) / ((3 * k : ℤ) : ℚ) := by
  have h₁ : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  field_simp [h₁, mul_assoc]
  <;> ring

lemma round1_h_eq2 (u : ℕ)
  (h : u ≥ 2):
  let a : ℤ := (u : ℤ)
  let b : ℤ := (u * (u + 1) : ℕ)
  let c : ℤ := (u + 1 : ℕ)
  (a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ (1 : ℚ) / (a : ℚ) = (1 : ℚ) / (b : ℚ) + (1 : ℚ) / (c : ℚ)) := by
  let a : ℤ := (u : ℤ)
  let b : ℤ := (u * (u + 1) : ℕ)
  let c : ℤ := (u + 1 : ℕ)
  have h1 : u ≥ 2 := h
  have h2 : (u : ℤ) ≠ ((u * (u + 1) : ℕ) : ℤ) := by
    have h2₁ : (u : ℕ) < u * (u + 1) := by nlinarith
    exact_mod_cast h2₁.ne
  have h3 : (u : ℤ) ≠ ((u + 1 : ℕ) : ℤ) := by
    have h3₁ : (u : ℤ) < ((u + 1 : ℕ) : ℤ) := by
      simp [h1] <;> linarith
    exact h3₁.ne
  have h4₁ : u * (u + 1) > u + 1 := by nlinarith
  have h4 : ((u * (u + 1) : ℕ) : ℤ) ≠ ((u + 1 : ℕ) : ℤ) := by
    intro h42
    have h43 : u * (u + 1) = u + 1 := by exact_mod_cast h42
    nlinarith
  have h5 : (1 : ℚ) / ((u : ℤ) : ℚ) = (1 : ℚ) / (((u * (u + 1) : ℕ) : ℤ) : ℚ) + (1 : ℚ) / (((u + 1 : ℕ) : ℤ) : ℚ) := by
    simpa [Int.cast_natCast] using round1_h_main_8dac98 u (show 1 ≤ u from by linarith)
  exact ⟨h2, h3, h4, h5⟩

theorem lemma_sum_of_two_naturals_ge_one (u v : ℕ)
  (hu_ge_1 : 1 ≤ u)
  (hv_ge_1 : 1 ≤ v):
  1 ≤ u + v := by
  classical
  have h1 : 1 ≤ u := hu_ge_1
  have h2 : 1 ≤ v := hv_ge_1
  have h3 : 1 ≤ u + v := by linarith
  have h4 : u * v > 0 := by
    exact round1_h2 u v h1 h2
  simp_all [round1_h_main_8dac98]
  <;> omega

lemma round1_h1_12976d (u v S : ℕ)
  (h_u_lt_v : u < v)
  (h_v_le_S : v ≤ S):
  u ≤ S := by
  have h11 : u ≤ v := Nat.le_of_lt h_u_lt_v
  have h12 : u ≤ S := Nat.le_trans h11 h_v_le_S
  exact h12

theorem lemma_u_le_S_from_u_lt_v_and_v_le_S (u v S : ℕ)
  (h_u_lt_v : u < v)
  (h_v_le_S : v ≤ S):
  u ≤ S := by
  exact round1_h1_12976d u v S h_u_lt_v h_v_le_S

lemma round1_h_main_5b5de2 (a b : ℕ):
  max a b ≥ a ∧ max a b ≥ b := by
  have h1 : max a b ≥ a := by
    exact?
  have h2 : max a b ≥ b := by
    exact?
  exact ⟨h1, h2⟩

theorem lemma_max_preserves_both_inequalities (a b : ℕ):
  max a b ≥ a ∧ max a b ≥ b := by
  have h1 : max a b ≥ a := by
    exact?
  have h2 : max a b ≥ b := by
    exact?
  exact ⟨h1, h2⟩

lemma factorial_ge_one (S : ℕ):
  Nat.factorial S ≥ 1 := by
  have h1 : Nat.factorial S > 0 := Nat.factorial_pos S
  omega

theorem round1_factorial_ge_one (S : ℕ)
  (hS : S ≥ 1):
  Nat.factorial S ≥ 1 := by
  have h1 : Nat.factorial S > 0 := Nat.factorial_pos S
  have h2 : Nat.factorial S ≥ 1 := by
    omega
  exact h2

theorem lemma_factorial_is_at_least_one_when_S_ge_one (S : ℕ)
  (hS : S ≥ 1):
  Nat.factorial S ≥ 1 := by
  exact round1_factorial_ge_one S hS

lemma round1_h1_f6e255 (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hu_dvd_N : u ∣ N):
  N / u ≥ 1 := by
  by_contra h
  have h' : N / u < 1 := by exact?
  have h'' : N / u = 0 := by
    simpa [Nat.lt_one_iff] using h'
  have h₂ : u * (N / u) = N := Nat.mul_div_cancel' hu_dvd_N
  rw [h''] at h₂
  have h₃ : N = 0 := by linarith
  omega

lemma round1_h2_177510 (N u v : ℕ)
  (hN : N ≥ 1)
  (hv : v ≥ 1)
  (hv_dvd_N : v ∣ N):
  N / v ≥ 1 := by
  by_contra h
  have h' : N / v < 1 := by exact?
  have h'' : N / v = 0 := by
    simpa [Nat.lt_one_iff] using h'
  have h₂ : v * (N / v) = N := Nat.mul_div_cancel' hv_dvd_N
  rw [h''] at h₂
  have h₃ : N = 0 := by linarith
  omega

lemma round1_h3 (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (hsum_dvd_N : (u + v) ∣ N):
  N / (u + v) ≥ 1 := by
  have huv_pos : u + v ≥ 1 := by omega
  by_contra h
  have h' : N / (u + v) < 1 := by exact?
  have h'' : N / (u + v) = 0 := by
    simpa [Nat.lt_one_iff] using h'
  have h₂ : (u + v) * (N / (u + v)) = N := Nat.mul_div_cancel' hsum_dvd_N
  rw [h''] at h₂
  have h₃ : N = 0 := by linarith
  omega

theorem positivity_of_N_div_u_N_div_v_N_div_u_plus_v (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N)
  (hsum_dvd_N : (u + v) ∣ N):
  N / u ≥ 1 ∧ N / v ≥ 1 ∧ N / (u + v) ≥ 1 := by
  have h1 : N / u ≥ 1 := round1_h1_f6e255 N u v hN hu hu_dvd_N
  have h2 : N / v ≥ 1 := round1_h2_177510 N u v hN hv hv_dvd_N
  have h3 : N / (u + v) ≥ 1 := round1_h3 N u v hN hu hv hsum_dvd_N
  exact ⟨h1, h2, h3⟩

lemma round1_h_main_2b5efa (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_ne : u ≠ v)
  (h_lt1 : u < v)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N):
  N / u ≠ N / v := by
  by_contra h
  have h1 : N = u * (N / u) := by
    rw [Nat.mul_div_cancel' hu_dvd_N]
  have h2 : N = v * (N / v) := by
    rw [Nat.mul_div_cancel' hv_dvd_N]
  have h3 : N = v * (N / u) := by
    have h4 : N / v = N / u := by exact h.symm
    rw [h4] at h2
    exact h2
  have h4 : u * (N / u) = v * (N / u) := by
    linarith
  have h5 : N / u > 0 := by
    apply Nat.pos_of_ne_zero
    intro h6
    have h7 : N / u = 0 := h6
    rw [h7] at h1
    omega
  have h8 : u = v := by
    apply Nat.eq_of_mul_eq_mul_right h5
    linarith
  linarith

lemma round1_h_main2 (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_ne : u ≠ v)
  (h_lt1 : u < v)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N):
  N / u > N / v := by
  have h1 : N = u * (N / u) := by
    rw [Nat.mul_div_cancel' hu_dvd_N]
  have h2 : N = v * (N / v) := by
    rw [Nat.mul_div_cancel' hv_dvd_N]
  by_contra h
  have h3 : N / u ≤ N / v := by omega
  have h4 : u * (N / u) ≤ u * (N / v) := by
    exact Nat.mul_le_mul_left u h3
  have h5 : u * (N / v) < v * (N / v) := by
    have h6 : u < v := h_lt1
    have h7 : 0 < N / v := by
      apply Nat.pos_of_ne_zero
      intro h8
      have h9 : N / v = 0 := h8
      rw [h9] at h2
      omega
    nlinarith
  have h6 : u * (N / u) < v * (N / v) := by
    linarith
  rw [h1, h2] at h6
  <;> omega

theorem distinctness_of_N_div_u_and_N_div_v (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_ne : u ≠ v)
  (h_lt1 : u < v)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N):
  N / u ≠ N / v := by
  exact round1_h_main_2b5efa N u v hN hu hv h_ne h_lt1 hu_dvd_N hv_dvd_N

lemma round1_h1_482eb5 (N u v : ℕ)
  (hu : u ≥ 1)
  (hu_dvd_N : u ∣ N):
  u * (N / u) = N := by
  have hhu_pos : 0 < u := by linarith
  have h : u * (N / u) = N := Nat.mul_div_cancel' hu_dvd_N
  exact h

lemma round1_h2_d2361a (N u v : ℕ)
  (hv : v ≥ 1)
  (hv_dvd_N : v ∣ N):
  v * (N / v) = N := by
  have hhv_pos : 0 < v := by linarith
  have h : v * (N / v) = N := Nat.mul_div_cancel' hv_dvd_N
  exact h

lemma round1_h3_559bca (N u v : ℕ)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (hsum_dvd_N : (u + v) ∣ N):
  (u + v) * (N / (u + v)) = N := by
  have hsum_pos : 0 < u + v := by linarith
  have h : (u + v) * (N / (u + v)) = N := Nat.mul_div_cancel' hsum_dvd_N
  exact h

theorem algebraic_identity_for_N_div_candidates (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N)
  (hsum_dvd_N : (u + v) ∣ N):
  (N / (u + v)) * ((N / u) + (N / v)) = (N / u) * (N / v) := by
  let x := N / u
  let y := N / v
  let z := N / (u + v)
  have h1 : u * x = N := round1_h1_482eb5 N u v hu hu_dvd_N
  have h2 : v * y = N := round1_h2_d2361a N u v hv hv_dvd_N
  have h3 : (u + v) * z = N := round1_h3_559bca N u v hu hv hsum_dvd_N
  have h_main : u * v * (z * (x + y)) = u * v * (x * y) := by
    have h4 : u * v * (z * (x + y)) = z * N * (u + v) := by
      calc
        u * v * (z * (x + y))
          = u * v * (z * x + z * y) := by ring
        _ = u * v * (z * x) + u * v * (z * y) := by ring
        _ = (v * z * (u * x)) + (u * z * (v * y)) := by ring
        _ = (v * z * N) + (u * z * N) := by
          rw [h1, h2]
          <;> ring
        _ = z * N * (u + v) := by ring
    have h5 : u * v * (x * y) = N * N := by
      calc
        u * v * (x * y) = (u * x) * (v * y) := by ring
        _ = N * N := by rw [h1, h2] <;> ring
    have h6 : z * N * (u + v) = N * N := by
      have h7 : z * (u + v) = N := by
        linarith
      calc
        z * N * (u + v) = N * (z * (u + v)) := by ring
        _ = N * N := by rw [h7] <;> ring
    rw [h4, h5, h6]
  have h_pos : 0 < u * v := by positivity
  have h_final : z * (x + y) = x * y := by
    apply mul_left_cancel₀ (show (u * v : ℕ) ≠ 0 by positivity)
    exact h_main
  simpa [x, y, z] using h_final

lemma round1_main_2cefd3 (χ : ℕ → ℤ)
  (N u v : ℕ)
  (h_color : χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v))):
  χ (N / (u + v)) = χ (N / u) ∧ χ (N / u) = χ (N / v) := by
  have h1 : χ (N / u) = χ (N / v) := h_color.1
  have h2 : χ (N / v) = χ (N / (u + v)) := h_color.2
  have h3 : χ (N / (u + v)) = χ (N / v) := by
    exact h2.symm
  have h4 : χ (N / (u + v)) = χ (N / u) := by
    calc
      χ (N / (u + v)) = χ (N / v) := h3
      _ = χ (N / u) := by
        exact h1.symm
  exact ⟨h4, h1⟩

theorem coloring_A_B_C_from_hypothesis (χ : ℕ → ℤ)
  (N u v : ℕ)
  (h_color : χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v))):
  χ (N / (u + v)) = χ (N / u) ∧ χ (N / u) = χ (N / v) := by
  exact round1_main_2cefd3 χ N u v h_color

lemma round1_h_B_gt_A (A B C : ℕ)
  (hA : A ≥ 1)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_eq : A * (B + C) = B * C):
  B > A := by
  by_contra h
  have h₁ : B ≤ A := by linarith
  have h₂ : A * (B + C) ≥ B * (B + C) := by
    exact mul_le_mul_of_nonneg_right h₁ (by positivity)
  have h₃ : A * (B + C) = B * C := h_eq
  have h₄ : B * (B + C) ≤ B * C := by linarith
  have h₅ : B ^ 2 + B * C ≤ B * C := by
    ring_nf at h₄ ⊢ <;> linarith
  have h₆ : B ^ 2 ≤ 0 := by linarith
  have h₇ : B ^ 2 ≥ 1 := by
    nlinarith
  linarith

lemma round1_h_C_gt_A (A B C : ℕ)
  (hA : A ≥ 1)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_eq : A * (B + C) = B * C):
  C > A := by
  by_contra h
  have h₁ : C ≤ A := by linarith
  have h₂ : A * (B + C) ≥ C * (B + C) := by
    exact mul_le_mul_of_nonneg_right h₁ (by positivity)
  have h₃ : A * (B + C) = B * C := h_eq
  have h₄ : C * (B + C) ≤ B * C := by linarith
  have h₅ : C * B + C ^ 2 ≤ B * C := by
    ring_nf at h₄ ⊢ <;> linarith
  have h₆ : C ^ 2 ≤ 0 := by linarith
  have h₇ : C ^ 2 ≥ 1 := by nlinarith
  linarith

lemma round1_h_main_e7b016 (A B C : ℕ)
  (hA : A ≥ 1)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_eq : A * (B + C) = B * C)
  (h_B_gt_A : B > A)
  (h_C_gt_A : C > A):
  (B - A) * (C - A) = A ^ 2 := by
  have h₁ : ∃ x : ℕ, B = x + A := by
    refine' ⟨B - A, _⟩
    omega
  have h₂ : ∃ y : ℕ, C = y + A := by
    refine' ⟨C - A, _⟩
    omega
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  have h₃ : B = x + A := hx
  have h₄ : C = y + A := hy
  have h₅ : A * (B + C) = B * C := h_eq
  rw [h₃, h₄] at h₅
  have h₆ : (x + A) * (y + A) = A * ((x + A) + (y + A)) := by
    linarith
  have h₇ : x * y = A ^ 2 := by
    ring_nf at h₆ ⊢ <;> nlinarith
  have h₈ : (B - A) = x := by omega
  have h₉ : (C - A) = y := by omega
  rw [h₈, h₉]
  exact h₇

theorem algebraic_manipulation_inequality_and_product (A B C : ℕ)
  (hA : A ≥ 1)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_eq : A * (B + C) = B * C):
  B > A ∧ C > A ∧ (B - A) * (C - A) = A^2 := by
  have h_B_gt_A : B > A := by
    exact round1_h_B_gt_A A B C hA hB hC h_eq
  have h_C_gt_A : C > A := by
    exact round1_h_C_gt_A A B C hA hB hC h_eq
  have h_main : (B - A) * (C - A) = A ^ 2 := by
    exact round1_h_main_e7b016 A B C hA hB hC h_eq h_B_gt_A h_C_gt_A
  exact ⟨h_B_gt_A, h_C_gt_A, h_main⟩

lemma round1_h_sum1 (v₁ v₂ v₃ : ℕ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃):
  (v₂ - v₁) + (v₃ - v₂) = v₃ - v₁ := by
  omega

lemma round1_h_sum2 (v₂ v₃ v₄ : ℕ)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄):
  (v₃ - v₂) + (v₄ - v₃) = v₄ - v₂ := by
  omega

lemma round1_h_sum3 (v₁ v₂ v₃ v₄ : ℕ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄):
  (v₂ - v₁) + (v₃ - v₂) + (v₄ - v₃) = v₄ - v₁ := by
  omega

theorem monochromatic_clique_differences_are_uniform (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ : ℕ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (c : ℤ)
  (h_c1 : φ (v₂ - v₁) = c)
  (h_c2 : φ (v₃ - v₂) = c)
  (h_c3 : φ (v₄ - v₃) = c)
  (h_c4 : φ (v₃ - v₁) = c)
  (h_c5 : φ (v₄ - v₂) = c)
  (h_c6 : φ (v₄ - v₁) = c):
  let x₁ := v₂ - v₁;
  let x₂ := v₃ - v₂;
  let x₃ := v₄ - v₃;
  φ x₁ = c ∧ φ x₂ = c ∧ φ x₃ = c ∧ φ (x₁ + x₂) = c ∧ φ (x₂ + x₃) = c ∧ φ (x₁ + x₂ + x₃) = c := by
  have h_sum1 : (v₂ - v₁) + (v₃ - v₂) = v₃ - v₁ := by
    exact round1_h_sum1 v₁ v₂ v₃ h1 h2
  have h_sum2 : (v₃ - v₂) + (v₄ - v₃) = v₄ - v₂ := by
    exact round1_h_sum2 v₂ v₃ v₄ h2 h3
  have h_sum3 : (v₂ - v₁) + (v₃ - v₂) + (v₄ - v₃) = v₄ - v₁ := by
    exact round1_h_sum3 v₁ v₂ v₃ v₄ h1 h2 h3
  dsimp only
  constructor
  · exact h_c1
  constructor
  · exact h_c2
  constructor
  · exact h_c3
  constructor
  · rw [h_sum1]
    exact h_c4
  constructor
  · rw [h_sum2]
    exact h_c5
  · rw [h_sum3]
    exact h_c6

lemma round1_main_d0e6f5 (φ : ℕ → ℤ)
  (x₁ x₂ x₃ S : ℕ)
  (hx1_ge_1 : x₁ ≥ 1)
  (hx2_ge_1 : x₂ ≥ 1)
  (hx3_ge_1 : x₃ ≥ 1)
  (c : ℤ)
  (h1 : φ x₁ = c)
  (h2 : φ x₂ = c)
  (h3 : φ x₃ = c)
  (h4 : φ (x₁ + x₂) = c)
  (h5 : φ (x₂ + x₃) = c)
  (h6 : φ (x₁ + x₂ + x₃) = c)
  (h_sum_le_S : x₁ + x₂ + x₃ ≤ S):
  ∃ (u v : ℕ),
    1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
  by_cases h : x₃ < x₁ + x₂
  ·
    refine' ⟨x₃, x₁ + x₂, by linarith, by linarith, h, by linarith, ?_⟩
    constructor
    ·
      rw [h3, h4]
    ·
      have h7 : x₃ + (x₁ + x₂) = x₁ + x₂ + x₃ := by
        omega
      have h8 : φ (x₃ + (x₁ + x₂)) = φ (x₁ + x₂ + x₃) := by rw [h7]
      have h9 : φ (x₃ + (x₁ + x₂)) = c := by
        rw [h8, h6]
      rw [h4, h9]
  ·
    have h' : x₃ ≥ x₁ + x₂ := by linarith
    have h4' : x₁ < x₂ + x₃ := by linarith
    refine' ⟨x₁, x₂ + x₃, by linarith, by linarith, h4', by linarith, ?_⟩
    constructor
    ·
      rw [h1, h5]
    ·
      have h10 : x₁ + (x₂ + x₃) = x₁ + x₂ + x₃ := by
        omega
      have h11 : φ (x₁ + (x₂ + x₃)) = φ (x₁ + x₂ + x₃) := by rw [h10]
      have h12 : φ (x₁ + (x₂ + x₃)) = c := by
        rw [h11, h6]
      rw [h5, h12]

theorem monochromatic_differences_produces_solution (φ : ℕ → ℤ)
  (x₁ x₂ x₃ S : ℕ)
  (hx1_ge_1 : x₁ ≥ 1)
  (hx2_ge_1 : x₂ ≥ 1)
  (hx3_ge_1 : x₃ ≥ 1)
  (c : ℤ)
  (h1 : φ x₁ = c)
  (h2 : φ x₂ = c)
  (h3 : φ x₃ = c)
  (h4 : φ (x₁ + x₂) = c)
  (h5 : φ (x₂ + x₃) = c)
  (h6 : φ (x₁ + x₂ + x₃) = c)
  (h_sum_le_S : x₁ + x₂ + x₃ ≤ S):
  ∃ (u v : ℕ),
    1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
  exact round1_main_d0e6f5 φ x₁ x₂ x₃ S hx1_ge_1 hx2_ge_1 hx3_ge_1 c h1 h2 h3 h4 h5 h6 h_sum_le_S

lemma round1_h_main_97b9ea :
  ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
  intro k a b
  have h : Nat.gcd (k * a) (k * b) = Nat.gcd (k * a) (k * b) := rfl
  exact?

theorem gcd_mul_distributive :
  ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
  intro k a b
  have h₁ : Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
    exact?
  exact h₁

lemma round1_h1_a8d611 (a b : ℕ):
  (Nat.gcd a b)^2 ∣ Nat.gcd (a^2) (b^2) := by
  let d := Nat.gcd a b
  have h_da : d ∣ a := Nat.gcd_dvd_left a b
  have h_db : d ∣ b := Nat.gcd_dvd_right a b
  rcases h_da with ⟨a', ha⟩
  rcases h_db with ⟨b', hb⟩
  have h1 : a ^ 2 = d ^ 2 * (a') ^ 2 := by
    rw [ha]
    <;> ring
  have h2 : b ^ 2 = d ^ 2 * (b') ^ 2 := by
    rw [hb]
    <;> ring
  have h3 : d ^ 2 ∣ a ^ 2 := by
    rw [h1]
    <;> exact dvd_mul_right (d ^ 2) ((a') ^ 2)
  have h4 : d ^ 2 ∣ b ^ 2 := by
    rw [h2]
    <;> exact dvd_mul_right (d ^ 2) ((b') ^ 2)
  have h5 : d ^ 2 ∣ Nat.gcd (a ^ 2) (b ^ 2) := Nat.dvd_gcd h3 h4
  exact h5

theorem gcd_of_squares_is_square_of_gcd :
  ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2 := by
  intro a b
  let d := Nat.gcd a b
  have h_da : d ∣ a := Nat.gcd_dvd_left a b
  have h_db : d ∣ b := Nat.gcd_dvd_right a b
  rcases h_da with ⟨a', ha⟩
  rcases h_db with ⟨b', hb⟩
  have h_eqa : a = d * a' := by exact ha
  have h_eqb : b = d * b' := by exact hb
  have h_main_goal : Nat.gcd (a^2) (b^2) = d^2 := by
    by_cases h_d : d = 0
    ·
      have h_gcd0 : Nat.gcd a b = 0 := by
        simpa [show Nat.gcd a b = d by rfl] using h_d
      have h_ab0 : a = 0 ∧ b = 0 := Nat.gcd_eq_zero_iff.mp h_gcd0
      have ha0 : a = 0 := h_ab0.1
      have hb0 : b = 0 := h_ab0.2
      have h1 : Nat.gcd (a^2) (b^2) = 0 := by
        rw [ha0, hb0]
        <;> simp
      have h2 : d ^ 2 = 0 := by
        rw [h_d] <;> simp
      rw [h1, h2]
    ·
      have h_pos : 0 < d := Nat.pos_of_ne_zero h_d
      have h1 : Nat.gcd a b = Nat.gcd (d * a') (d * b') := by
        rw [h_eqa, h_eqb]
      have h2 : Nat.gcd (d * a') (d * b') = d * Nat.gcd a' b' := by
        simp [Nat.gcd_mul_left]
      have h_eq : Nat.gcd a b = d * Nat.gcd a' b' := by
        rw [h1, h2]
      have h3 : d = d * Nat.gcd a' b' := by
        simpa [show Nat.gcd a b = d by rfl] using h_eq
      have h4 : Nat.gcd a' b' = 1 := by
        have h5 : d * 1 = d * Nat.gcd a' b' := by
          simpa using h3
        have h6 : 1 = Nat.gcd a' b' := by
          apply Nat.mul_left_cancel h_pos
          simpa using h5
        exact h6.symm
      have h_main : Nat.gcd ((a')^2) ((b')^2) = 1 := by
        simpa [Nat.coprime_iff_gcd_eq_one] using Nat.Coprime.pow 2 2 (Nat.coprime_iff_gcd_eq_one.mpr h4)
      have h9 : Nat.gcd (a^2) (b^2) = Nat.gcd ((d^2 * (a')^2)) ((d^2 * (b')^2)) := by
        have h10 : a^2 = d^2 * (a')^2 := by
          rw [h_eqa] <;> ring
        have h11 : b^2 = d^2 * (b')^2 := by
          rw [h_eqb] <;> ring
        rw [h10, h11]
      rw [h9]
      have h12 : Nat.gcd (d^2 * (a')^2) (d^2 * (b')^2) = d^2 * Nat.gcd ((a')^2) ((b')^2) := by
        simp [Nat.gcd_mul_left]
      rw [h12, h_main]
      <;> simp
  have h_final : Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2 := by
    simpa [show Nat.gcd a b = d by rfl] using h_main_goal
  exact h_final

lemma round1_h_main_afd5c3 (u s : ℕ)
  (hu : u ≥ 1)
  (h_eq : (Nat.gcd u s)^2 = u):
  Nat.gcd u s ≥ 1 := by
  have h1 : Nat.gcd u s ∣ u := Nat.gcd_dvd_left u s
  have h2 : Nat.gcd u s ≠ 0 := by
    by_contra h
    rw [h] at h1
    have h3 : 0 ∣ u := h1
    have h4 : u = 0 := by simpa using h3
    linarith
  have h5 : Nat.gcd u s ≥ 1 := by
    omega
  exact h5

theorem gcd_is_positive_of_square_eq (u s : ℕ)
  (hu : u ≥ 1)
  (h_eq : (Nat.gcd u s)^2 = u):
  Nat.gcd u s ≥ 1 := by
  exact round1_h_main_afd5c3 u s hu h_eq

lemma round1_h_main_69f37a (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1):
  ∃ (u' v' : ℕ), (Nat.gcd U V) * u' = U ∧ (Nat.gcd U V) * v' = V := by
  have h1 : (Nat.gcd U V) ∣ U := Nat.gcd_dvd_left U V
  have h2 : (Nat.gcd U V) ∣ V := Nat.gcd_dvd_right U V
  rcases h1 with ⟨u', hu'⟩
  rcases h2 with ⟨v', hv'⟩
  refine' ⟨u', v', _⟩
  exact ⟨by linarith, by linarith⟩

lemma round1_h_pos (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (u' v' : ℕ)
  (hu' : (Nat.gcd U V) * u' = U)
  (hv' : (Nat.gcd U V) * v' = V):
  u' ≥ 1 ∧ v' ≥ 1 := by
  have h_u_pos : u' ≥ 1 := by
    by_contra h
    have h' : u' = 0 := by omega
    rw [h'] at hu'
    omega
  have h_v_pos : v' ≥ 1 := by
    by_contra h
    have h' : v' = 0 := by omega
    rw [h'] at hv'
    omega
  exact ⟨h_u_pos, h_v_pos⟩

theorem existence_of_u_prime_v_prime (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1):
  ∃ u' v' : ℕ,
    u' ≥ 1 ∧
    v' ≥ 1 ∧
    (Nat.gcd U V) * u' = U ∧
    (Nat.gcd U V) * v' = V := by
  have h_main : ∃ (u' v' : ℕ), (Nat.gcd U V) * u' = U ∧ (Nat.gcd U V) * v' = V :=
    round1_h_main_69f37a U V hU hV
  rcases h_main with ⟨u', v', hu', hv'⟩
  have h_pos : u' ≥ 1 ∧ v' ≥ 1 := round1_h_pos U V hU hV u' v' hu' hv'
  refine' ⟨u', v', h_pos.1, h_pos.2, hu', hv'⟩

lemma round1_coprime_after_division_by_gcd (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (u' v' : ℕ)
  (h1 : (Nat.gcd U V) * u' = U)
  (h2 : (Nat.gcd U V) * v' = V):
  Nat.gcd u' v' = 1 := by
  let g := Nat.gcd U V
  have hg_pos : g > 0 := Nat.gcd_pos_of_pos_left V hU
  let d := Nat.gcd u' v'
  have h_d_div_u' : d ∣ u' := Nat.gcd_dvd_left u' v'
  have h_d_div_v' : d ∣ v' := Nat.gcd_dvd_right u' v'
  have h_gd_div_U : g * d ∣ U := by
    have h3 : g * d ∣ g * u' := mul_dvd_mul_left g h_d_div_u'
    rw [h1] at *
    exact h3
  have h_gd_div_V : g * d ∣ V := by
    have h4 : g * d ∣ g * v' := mul_dvd_mul_left g h_d_div_v'
    rw [h2] at *
    exact h4
  have h_gd_div_g : g * d ∣ g := Nat.dvd_gcd h_gd_div_U h_gd_div_V
  have h_d_div_1 : d ∣ 1 := by
    rcases h_gd_div_g with ⟨k, hk⟩
    have h_eq : g = (g * d) * k := by linarith
    have h_eq' : g = g * (d * k) := by
      ring_nf at h_eq ⊢ <;> linarith
    have h1 : 1 = d * k := by
      apply Nat.eq_of_mul_eq_mul_left hg_pos
      linarith
    have h2 : d ∣ 1 := by
      use k
      <;> linarith
    exact h2
  have h_d_eq_1 : d = 1 := by
    exact Nat.eq_one_of_dvd_one h_d_div_1
  exact h_d_eq_1

theorem coprime_after_division_by_gcd (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (u' v' : ℕ)
  (h1 : (Nat.gcd U V) * u' = U)
  (h2 : (Nat.gcd U V) * v' = V):
  Nat.gcd u' v' = 1 := by
  exact round1_coprime_after_division_by_gcd U V hU hV u' v' h1 h2

lemma round1_square_divides_square_implies_divides (x y : ℕ)
  (h : x^2 ∣ y^2):
  x ∣ y := by
  have h_main : x ^ 2 ∣ y ^ 2 := h
  have h₂ : (2 : ℕ) ≠ 0 := by norm_num
  have h₃ : (x ^ 2 ∣ y ^ 2) ↔ (x ∣ y) := by
    exact?
  exact h₃.mp h_main

theorem square_divides_square_implies_divides (x y : ℕ)
  (h : x^2 ∣ y^2):
  x ∣ y := by
  exact round1_square_divides_square_implies_divides x y h

lemma round1_h_main_f822a5 (U V A : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (hA : A ≥ 1)
  (h_prod : U * V = A^2)
  (u' v' : ℕ)
  (h1 : (Nat.gcd U V) * u' = U)
  (h2 : (Nat.gcd U V) * v' = V):
  (Nat.gcd U V)^2 ∣ A^2 := by
  have h5 : U * V = (Nat.gcd U V)^2 * (u' * v') := by
    calc
      U * V
        = ((Nat.gcd U V) * u') * ((Nat.gcd U V) * v') := by rw [h1, h2]
      _ = (Nat.gcd U V)^2 * (u' * v') := by ring
  have h6 : A^2 = (Nat.gcd U V)^2 * (u' * v') := by
    rw [←h_prod, h5]
  rw [h6]
  <;> exact ⟨u' * v', by ring⟩

theorem gcd_sq_divides_A_sq (U V A : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (hA : A ≥ 1)
  (h_prod : U * V = A^2)
  (u' v' : ℕ)
  (h1 : (Nat.gcd U V) * u' = U)
  (h2 : (Nat.gcd U V) * v' = V):
  (Nat.gcd U V)^2 ∣ A^2 := by
  exact round1_h_main_f822a5 U V A hU hV hA h_prod u' v' h1 h2

lemma round1_empty_C_case_lemma (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_empty : C = ∅):
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (v₁ v₂ v₃ v₄ : ℕ),
          v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
          ∃ (c : ℤ),
            φ (v₂ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₃) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₁) = c := by
  use 0
  intro S hS φ hφ
  have h₁ : ∀ (n : ℕ), φ n ∈ C := hφ
  have h₂ : φ 0 ∈ C := h₁ 0
  rw [hC_empty] at h₂
  <;> simp at h₂
  <;> tauto

theorem empty_C_case_lemma (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_empty : C = ∅):
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (v₁ v₂ v₃ v₄ : ℕ),
          v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
          ∃ (c : ℤ),
            φ (v₂ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₃) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₁) = c := by
  exact round1_empty_C_case_lemma C hC_finite hC_empty

lemma round1_clique_to_differences (v₁ v₂ v₃ v₄ : ℕ)
  (φ : ℕ → ℤ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : ∀ (x y : ℕ), x ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → y ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → x < y → φ (y - x) = c):
  φ (v₂ - v₁) = c ∧ φ (v₃ - v₂) = c ∧ φ (v₄ - v₃) = c ∧ φ (v₃ - v₁) = c ∧ φ (v₄ - v₂) = c ∧ φ (v₄ - v₁) = c := by
  have h5 : φ (v₂ - v₁) = c := by
    apply h4 v₁ v₂
    <;> simp [h1]
    <;> tauto
  have h6 : φ (v₃ - v₂) = c := by
    apply h4 v₂ v₃
    <;> simp [h2]
    <;> tauto
  have h7 : φ (v₄ - v₃) = c := by
    apply h4 v₃ v₄
    <;> simp [h3]
    <;> tauto
  have h8 : v₁ < v₃ := by linarith
  have h9 : φ (v₃ - v₁) = c := by
    apply h4 v₁ v₃
    <;> simp [h8]
    <;> tauto
  have h10 : v₂ < v₄ := by linarith
  have h11 : φ (v₄ - v₂) = c := by
    apply h4 v₂ v₄
    <;> simp [h10]
    <;> tauto
  have h12 : v₁ < v₄ := by linarith
  have h13 : φ (v₄ - v₁) = c := by
    apply h4 v₁ v₄
    <;> simp [h12]
    <;> tauto
  exact ⟨h5, h6, h7, h9, h11, h13⟩

theorem clique_to_differences_lemma (v₁ v₂ v₃ v₄ : ℕ)
  (φ : ℕ → ℤ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : ∀ (x y : ℕ), x ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → y ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → x < y → φ (y - x) = c):
  φ (v₂ - v₁) = c ∧ φ (v₃ - v₂) = c ∧ φ (v₄ - v₃) = c ∧ φ (v₃ - v₁) = c ∧ φ (v₄ - v₂) = c ∧ φ (v₄ - v₁) = c := by
  have h5 : φ (v₂ - v₁) = c := by
    apply h4 v₁ v₂
    <;> simp [h1]
    <;> tauto
  have h6 : φ (v₃ - v₂) = c := by
    apply h4 v₂ v₃
    <;> simp [h2]
    <;> tauto
  have h7 : φ (v₄ - v₃) = c := by
    apply h4 v₃ v₄
    <;> simp [h3]
    <;> tauto
  have h8 : v₁ < v₃ := by linarith
  have h9 : φ (v₃ - v₁) = c := by
    apply h4 v₁ v₃
    <;> simp [h8]
    <;> tauto
  have h10 : v₂ < v₄ := by linarith
  have h11 : φ (v₄ - v₂) = c := by
    apply h4 v₂ v₄
    <;> simp [h10]
    <;> tauto
  have h12 : v₁ < v₄ := by linarith
  have h13 : φ (v₄ - v₁) = c := by
    apply h4 v₁ v₄
    <;> simp [h12]
    <;> tauto
  exact ⟨h5, h6, h7, h9, h11, h13⟩

lemma round1_h_main_312fa6 (u s : ℕ)
  (h_gcd_of_squares : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2):
  (Nat.gcd u s)^2 = Nat.gcd (u^2) (s^2) := by
  have h1 : Nat.gcd (u^2) (s^2) = (Nat.gcd u s)^2 := h_gcd_of_squares u s
  rw [eq_comm] at h1
  exact h1

theorem gcd_sq_eq_gcd_of_squares (u s : ℕ)
  (h_gcd_of_squares : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2):
  (Nat.gcd u s)^2 = Nat.gcd (u^2) (s^2) := by
  exact round1_h_main_312fa6 u s h_gcd_of_squares

lemma round1_gcd_u2_s2_eq_gcd_u2_uv (u v s : ℕ)
  (h_prod : u * v = s^2):
  Nat.gcd (u^2) (s^2) = Nat.gcd (u^2) (u * v) := by
  have h1 : s ^ 2 = u * v := by
    exact h_prod.symm
  rw [h1]
  <;> rfl

theorem gcd_u2_s2_eq_gcd_u2_uv (u v s : ℕ)
  (h_prod : u * v = s^2):
  Nat.gcd (u^2) (s^2) = Nat.gcd (u^2) (u * v) := by
  exact round1_gcd_u2_s2_eq_gcd_u2_uv u v s h_prod

theorem gcd_u2_uv_eq_u_gcd_u_v (u v : ℕ)
  (hu : u ≥ 1)
  (h_gcd_mul_distributive : ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b):
  Nat.gcd (u^2) (u * v) = u * Nat.gcd u v := by
  have h_main : Nat.gcd (u^2) (u * v) = u * Nat.gcd u v := by
    have h1 : Nat.gcd (u * u) (u * v) = u * Nat.gcd u v := h_gcd_mul_distributive u u v
    have h2 : u ^ 2 = u * u := by ring
    rw [h2]
    exact h1
  exact h_main

theorem square_gcd_v_s_is_gcd_v2_s2 (v s : ℕ)
  (h_gcd_of_squares : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2):
  (Nat.gcd v s)^2 = Nat.gcd (v^2) (s^2) := by
  have h1 : Nat.gcd (v^2) (s^2) = (Nat.gcd v s)^2 := h_gcd_of_squares v s
  exact h1.symm

lemma round1_h_main_bfa3e6 (u v s : ℕ)
  (h_prod : u * v = s^2):
  Nat.gcd (v^2) (s^2) = Nat.gcd (v^2) (u * v) := by
  have h1 : s ^ 2 = u * v := by
    exact h_prod.symm
  rw [h1]

theorem gcd_v2_s2_eq_gcd_v2_uv_from_prod (u v s : ℕ)
  (h_prod : u * v = s^2):
  Nat.gcd (v^2) (s^2) = Nat.gcd (v^2) (u * v) := by
  exact round1_h_main_bfa3e6 u v s h_prod

theorem gcd_v2_uv_eq_v_mul_gcd_v_u (u v : ℕ)
  (h_gcd_mul_distributive : ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b):
  Nat.gcd (v^2) (u * v) = v * Nat.gcd v u := by
  have h_main : Nat.gcd (v * v) (v * u) = v * Nat.gcd v u := by
    exact h_gcd_mul_distributive v v u
  have h₁ : Nat.gcd (v ^ 2) (u * v) = Nat.gcd (v * v) (v * u) := by
    ring_nf
    <;> rfl
  rw [h₁]
  exact h_main

lemma round1_h_main_cfa215 (u v : ℕ):
  v * Nat.gcd v u = v * Nat.gcd u v := by
  have h₁ : Nat.gcd v u = Nat.gcd u v := by
    simp [Nat.gcd_comm]
  rw [h₁]

theorem v_mul_gcd_v_u_eq_v_mul_gcd_u_v (u v : ℕ):
  v * Nat.gcd v u = v * Nat.gcd u v := by
  exact round1_h_main_cfa215 u v

lemma round1_v_mul_gcd_u_v_eq_v_of_coprime (u v : ℕ)
  (h_coprime : Nat.gcd u v = 1)
  (hv : v ≥ 1):
  v * Nat.gcd u v = v := by
  rw [h_coprime]
  <;> ring

theorem v_mul_gcd_u_v_eq_v_of_coprime (u v : ℕ)
  (h_coprime : Nat.gcd u v = 1)
  (hv : v ≥ 1):
  v * Nat.gcd u v = v := by
  exact round1_v_mul_gcd_u_v_eq_v_of_coprime u v h_coprime hv

lemma round1_h_main_9d6709 (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1):
  Nat.gcd U V ≥ 1 := by
  have h1 : Nat.gcd U V ∣ U := Nat.gcd_dvd_left U V
  have hU' : 0 < U := by linarith
  have h2 : 0 < Nat.gcd U V := Nat.pos_of_dvd_of_pos h1 hU'
  linarith

theorem lemma_gcd_ge_one (U V : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1):
  Nat.gcd U V ≥ 1 := by
  exact round1_h_main_9d6709 U V hU hV

theorem round1_lemma_A_eq_gcd_mul_s (A g : ℕ)
  (h_g_dvd_A : g ∣ A):
  ∃ s : ℕ, A = g * s := by
  obtain ⟨s, hs⟩ := h_g_dvd_A
  refine' ⟨s, _⟩
  linarith

theorem round1_h_gcd_dvd_x (x y : ℕ):
  Nat.gcd x y ∣ x := by
  exact Nat.gcd_dvd_left x y

theorem round1_h_gcd_dvd_y (x y : ℕ):
  Nat.gcd x y ∣ y := by
  exact Nat.gcd_dvd_right x y

theorem round1_h_main_effc97 (x y : ℕ):
  ∃ (g s t : ℕ), g = Nat.gcd x y ∧ x = g * s ∧ y = g * t := by
  use Nat.gcd x y
  have h1 : Nat.gcd x y ∣ x := round1_h_gcd_dvd_x x y
  have h2 : Nat.gcd x y ∣ y := round1_h_gcd_dvd_y x y
  have h3 : ∃ s : ℕ, x = (Nat.gcd x y) * s := round1_lemma_A_eq_gcd_mul_s x (Nat.gcd x y) h1
  have h4 : ∃ t : ℕ, y = (Nat.gcd x y) * t := round1_lemma_A_eq_gcd_mul_s y (Nat.gcd x y) h2
  rcases h3 with ⟨s, hs⟩
  rcases h4 with ⟨t, ht⟩
  refine' ⟨s, t, by simp, hs, ht⟩

theorem lemma_A_eq_gcd_mul_s (A g : ℕ)
  (h_g_dvd_A : g ∣ A):
  ∃ s : ℕ, A = g * s := by
  aesop

lemma round1_h_main_12a1d3 (u' v' s g : ℕ)
  (h_g_sq_ne_zero : g ^ 2 ≠ 0)
  (h_eq : g ^ 2 * (u' * v') = g ^ 2 * s ^ 2):
  u' * v' = s ^ 2 := by
  have h1 : g ^ 2 > 0 := by
    exact Nat.pos_of_ne_zero h_g_sq_ne_zero
  have h2 : g ^ 2 * (u' * v') = g ^ 2 * s ^ 2 := h_eq
  have h3 : u' * v' = s ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < g ^ 2 from h1)
    linarith
  exact h3

theorem lemma_cancel_eq_from_mul_eq (u' v' s g : ℕ)
  (h_g_sq_ne_zero : g ^ 2 ≠ 0)
  (h_eq : g ^ 2 * (u' * v') = g ^ 2 * s ^ 2):
  u' * v' = s ^ 2 := by
  exact round1_h_main_12a1d3 u' v' s g h_g_sq_ne_zero h_eq

lemma round1_h_main_b36ad5 (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_nonempty : C ≠ ∅):
  ∃ (k : ℕ), k ≥ 1 ∧ C.ncard = k := by
  have h1 : Set.Nonempty C := by
    exact?
  rcases h1 with ⟨x, hx⟩
  have h2 : C.ncard ≠ 0 := by
    exact Set.ncard_ne_zero_of_mem hx hC_finite
  have h3 : C.ncard ≥ 1 := by
    omega
  refine' ⟨C.ncard, h3, _⟩
  <;> rfl

theorem get_card_ge_one_from_finite_nonempty_set (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_nonempty : C ≠ ∅):
  ∃ (k : ℕ), k ≥ 1 ∧ C.ncard = k := by
  exact round1_h_main_b36ad5 C hC_finite hC_nonempty

theorem six_differences_monochromatic_entails_all_pairs_monochromatic (v₁ v₂ v₃ v₄ : ℕ)
  (c : ℤ)
  (φ : ℕ → ℤ)
  (h_order1 : v₁ < v₂)
  (h_order2 : v₂ < v₃)
  (h_order3 : v₃ < v₄)
  (h_diff1 : φ (v₂ - v₁) = c)
  (h_diff2 : φ (v₃ - v₁) = c)
  (h_diff3 : φ (v₄ - v₁) = c)
  (h_diff4 : φ (v₃ - v₂) = c)
  (h_diff5 : φ (v₄ - v₂) = c)
  (h_diff6 : φ (v₄ - v₃) = c):
  ∀ (x y : ℕ), x ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → y ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → x < y → φ (y - x) = c := by
  intro x y hx hy hxy
  have h1 : x = v₁ ∨ x = v₂ ∨ x = v₃ ∨ x = v₄ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    tauto
  have h2 : y = v₁ ∨ y = v₂ ∨ y = v₃ ∨ y = v₄ := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    tauto
  rcases h1 with (rfl | rfl | rfl | rfl)
  ·
    rcases h2 with (rfl | rfl | rfl | rfl)
    · exfalso
      linarith
    · simpa using h_diff1
    · simpa using h_diff2
    · simpa using h_diff3
  ·
    rcases h2 with (rfl | rfl | rfl | rfl)
    · exfalso
      linarith
    · exfalso
      linarith
    · simpa using h_diff4
    · simpa using h_diff5
  ·
    rcases h2 with (rfl | rfl | rfl | rfl)
    · exfalso
      linarith
    · exfalso
      linarith
    · exfalso
      linarith
    · simpa using h_diff6
  ·
    rcases h2 with (rfl | rfl | rfl | rfl)
    · exfalso
      linarith
    · exfalso
      linarith
    · exfalso
      linarith
    · exfalso
      linarith

theorem construct_edge_color_from_phi (C : Set ℤ)
  (hC_finite : C.Finite)
  (S : ℕ)
  (φ : ℕ → ℤ)
  (hφ : ∀ (n : ℕ), φ n ∈ C):
  ∃ (edge_color : ℕ → ℕ → ℤ),
    (∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u)) ∧
    (∀ (u v : ℕ), u < v → edge_color u v ∈ C) := by
  use fun u v : ℕ => if h : u < v then φ (v - u) else 0
  constructor
  ·
    intro u v huv hvS
    simp [huv]
    <;> aesop
  ·
    intro u v huv
    simp [huv]
    <;> exact hφ (v - u)

lemma round1_h11 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h5 : edge_color v₁ v₂ = c):
  φ (v₂ - v₁) = c := by
  have h111 : v₂ ≤ S := by linarith
  have h112 : edge_color v₁ v₂ = φ (v₂ - v₁) := h_edge_color_eq_phi v₁ v₂ h1 h111
  rw [h112] at h5
  exact h5

lemma round1_h12 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h6 : edge_color v₁ v₃ = c):
  φ (v₃ - v₁) = c := by
  have h121 : v₁ < v₃ := by linarith
  have h122 : v₃ ≤ S := by linarith
  have h123 : edge_color v₁ v₃ = φ (v₃ - v₁) := h_edge_color_eq_phi v₁ v₃ h121 h122
  rw [h123] at h6
  exact h6

lemma round1_h13 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h7 : edge_color v₁ v₄ = c):
  φ (v₄ - v₁) = c := by
  have h131 : v₁ < v₄ := by linarith
  have h132 : v₄ ≤ S := h4
  have h133 : edge_color v₁ v₄ = φ (v₄ - v₁) := h_edge_color_eq_phi v₁ v₄ h131 h132
  rw [h133] at h7
  exact h7

lemma round1_h14 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h8 : edge_color v₂ v₃ = c):
  φ (v₃ - v₂) = c := by
  have h141 : v₂ < v₃ := h2
  have h142 : v₃ ≤ S := by linarith
  have h143 : edge_color v₂ v₃ = φ (v₃ - v₂) := h_edge_color_eq_phi v₂ v₃ h141 h142
  rw [h143] at h8
  exact h8

lemma round1_h15 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h9 : edge_color v₂ v₄ = c):
  φ (v₄ - v₂) = c := by
  have h151 : v₂ < v₄ := by linarith
  have h152 : v₄ ≤ S := h4
  have h153 : edge_color v₂ v₄ = φ (v₄ - v₂) := h_edge_color_eq_phi v₂ v₄ h151 h152
  rw [h153] at h9
  exact h9

lemma round1_h16 (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h10 : edge_color v₃ v₄ = c):
  φ (v₄ - v₃) = c := by
  have h161 : v₃ < v₄ := h3
  have h162 : v₄ ≤ S := h4
  have h163 : edge_color v₃ v₄ = φ (v₄ - v₃) := h_edge_color_eq_phi v₃ v₄ h161 h162
  rw [h163] at h10
  exact h10

theorem monochromatic_clique_gives_6_differences (φ : ℕ → ℤ)
  (v₁ v₂ v₃ v₄ S : ℕ)
  (c : ℤ)
  (h1 : v₁ < v₂)
  (h2 : v₂ < v₃)
  (h3 : v₃ < v₄)
  (h4 : v₄ ≤ S)
  (edge_color : ℕ → ℕ → ℤ)
  (h_edge_color_eq_phi : ∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u))
  (h5 : edge_color v₁ v₂ = c)
  (h6 : edge_color v₁ v₃ = c)
  (h7 : edge_color v₁ v₄ = c)
  (h8 : edge_color v₂ v₃ = c)
  (h9 : edge_color v₂ v₄ = c)
  (h10 : edge_color v₃ v₄ = c):
  φ (v₂ - v₁) = c ∧
  φ (v₃ - v₁) = c ∧
  φ (v₄ - v₁) = c ∧
  φ (v₃ - v₂) = c ∧
  φ (v₄ - v₂) = c ∧
  φ (v₄ - v₃) = c := by
  have h11 : φ (v₂ - v₁) = c := round1_h11 φ v₁ v₂ v₃ v₄ S c h1 h2 h3 h4 edge_color h_edge_color_eq_phi h5
  have h12 : φ (v₃ - v₁) = c := round1_h12 φ v₁ v₂ v₃ v₄ S c h1 h2 h3 h4 edge_color h_edge_color_eq_phi h6
  have h13 : φ (v₄ - v₁) = c := round1_h13 φ v₁ v₂ v₃ v₄ S c h1 h2 h3 h4 edge_color h_edge_color_eq_phi h7
  have h14 : φ (v₃ - v₂) = c := round1_h14 φ v₁ v₂ v₃ v₄ S c h2 h3 h4 edge_color h_edge_color_eq_phi h8
  have h15 : φ (v₄ - v₂) = c := round1_h15 φ v₁ v₂ v₃ v₄ S c h2 h3 h4 edge_color h_edge_color_eq_phi h9
  have h16 : φ (v₄ - v₃) = c := round1_h16 φ v₁ v₂ v₃ v₄ S c h3 h4 edge_color h_edge_color_eq_phi h10
  exact ⟨h11, h12, h13, h14, h15, h16⟩

theorem color_set_bijection (k : ℕ)
  (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_card : C.ncard = k)
  (hk : k ≥ 1):
  ∃ (f : ℤ → ℕ) (g : ℕ → ℤ),
    (∀ (x : ℤ), x ∈ C → 1 ≤ f x ∧ f x ≤ k) ∧
    (∀ (i : ℕ), 1 ≤ i ∧ i ≤ k → g i ∈ C ∧ f (g i) = i) ∧
    (∀ (x : ℤ), x ∈ C → g (f x) = x) := by
  have hC_nonempty : Set.Nonempty C := by
    have h1 : 0 < C.ncard := by
      rw [hC_card]
      <;> omega
    have h2 : 0 < C.ncard := h1
    have h3 : C.Nonempty := by
      exact?
    exact h3
  haveI : DecidablePred (· ∈ C) := by exact?
  have h1 : ∃ (e : C ≃ Fin k), True := by
    let e₁ : C ≃ Fin (C.ncard) := hC_finite.equivFin C
    let e₂ : Fin (C.ncard) ≃ Fin k := by
      rw [hC_card]
      <;> simp
    refine ⟨e₁.trans e₂, trivial⟩
  rcases h1 with ⟨e, _⟩
  let f : ℤ → ℕ := fun x => if h : x ∈ C then (e ⟨x, h⟩).val + 1 else 1
  let g : ℕ → ℤ := fun i => if h1 : 1 ≤ i ∧ i ≤ k then (e.symm ⟨i - 1, by omega⟩).val else 0
  have h2 : ∀ (x : ℤ), x ∈ C → 1 ≤ f x ∧ f x ≤ k := by
    intro x hx
    have hfx : f x = (e ⟨x, hx⟩).val + 1 := by
      dsimp only [f]
      rw [dif_pos hx]
    rw [hfx]
    have h3 : (e ⟨x, hx⟩).val < k := Fin.is_lt (e ⟨x, hx⟩)
    omega
  have h3 : ∀ (i : ℕ), 1 ≤ i ∧ i ≤ k → g i ∈ C ∧ f (g i) = i := by
    intro i hi
    have h4 : 1 ≤ i := hi.1
    have h5 : i ≤ k := hi.2
    have h6 : i - 1 < k := by omega
    have h7 : g i = (e.symm ⟨i - 1, h6⟩).val := by
      dsimp only [g]
      have h8 : 1 ≤ i ∧ i ≤ k := hi
      rw [dif_pos h8]
    rw [h7]
    have h8 : (e.symm ⟨i - 1, h6⟩).val ∈ C := (e.symm ⟨i - 1, h6⟩).property
    have h9 : f ((e.symm ⟨i - 1, h6⟩).val) = i := by
      have h10 : f ((e.symm ⟨i - 1, h6⟩).val) = (e ⟨ (e.symm ⟨i - 1, h6⟩).val, h8⟩).val + 1 := by
        dsimp only [f]
        rw [dif_pos h8]
      rw [h10]
      have h11 : e ⟨ (e.symm ⟨i - 1, h6⟩).val, h8⟩ = (⟨i - 1, h6⟩ : Fin k) := by
        simpa [Equiv.symm_apply_apply] using e.apply_symm_apply ⟨i - 1, h6⟩
      rw [h11]
      <;> simp [Fin.ext_iff] <;> omega
    exact ⟨h8, h9⟩
  have h4 : ∀ (x : ℤ), x ∈ C → g (f x) = x := by
    intro x hx
    have h5 : f x = (e ⟨x, hx⟩).val + 1 := by
      dsimp only [f]
      rw [dif_pos hx]
    rw [h5]
    set i : ℕ := (e ⟨x, hx⟩).val + 1 with hi
    have h6 : 1 ≤ i := by omega
    have h7 : i ≤ k := by
      have h8 : (e ⟨x, hx⟩).val < k := Fin.is_lt (e ⟨x, hx⟩)
      omega
    have h9 : g i = (e.symm ⟨(e ⟨x, hx⟩).val, by omega⟩).val := by
      dsimp only [g]
      have h10 : 1 ≤ i ∧ i ≤ k := ⟨h6, h7⟩
      rw [dif_pos h10]
      <;> simp [hi]
      <;> omega
    rw [h9]
    have h10 : e.symm ⟨(e ⟨x, hx⟩).val, by omega⟩ = (⟨x, hx⟩ : C) := by
      simpa [Equiv.symm_apply_apply] using e.symm_apply_apply ⟨x, hx⟩
    rw [h10]
    <;> simp
  exact ⟨f, g, h2, h3, h4⟩

theorem round1_ramsey_base_case_s_or_t_eq_1 (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (h : s = 1 ∨ t = 1):
  ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
  (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
    (∀ (i j : Fin s), i < j → f i < f j) ∧
    (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color ( f i) (f j) = c2)) := by
  cases h with
  | inl h1 =>
    use 0
    intro S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2
    have h_main : ∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧ (∀ (i j : Fin s), i < j → f i < f j) ∧ (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1) := by
      subst h1
      let f : Fin 1 → ℕ := fun _ => 0
      have h1 : ∀ (i : Fin 1), f i ≤ S := by
        intro i
        fin_cases i <;> simp [f] <;> omega
      have h2 : ∀ (i j : Fin 1), i < j → f i < f j := by
        intro i j hlt
        fin_cases i <;> fin_cases j <;> simp_all (config := {decide := true})
      have h3 : ∀ (i j : Fin 1), i < j → edge_color (f i) (f j) = c1 := by
        intro i j hlt
        fin_cases i <;> fin_cases j <;> simp_all (config := {decide := true})
      refine' ⟨f, h1, h2, h3⟩
    exact Or.inl h_main
  | inr h2 =>
    use 0
    intro S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2
    have h_main : ∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧ (∀ (i j : Fin t), i < j → f i < f j) ∧ (∀ (i j : Fin t), i < j → edge_color ( (f i)) (f j) = c2) := by
      subst h2
      let f : Fin 1 → ℕ := fun _ => 0
      have h1 : ∀ (i : Fin 1), f i ≤ S := by
        intro i
        fin_cases i <;> simp [f] <;> omega
      have h2 : ∀ (i j : Fin 1), i < j → f i < f j := by
        intro i j hlt
        fin_cases i <;> fin_cases j <;> simp_all (config := {decide := true})
      have h3 : ∀ (i j : Fin 1), i < j → edge_color (f i) (f j) = c2 := by
        intro i j hlt
        fin_cases i <;> fin_cases j <;> simp_all (config := {decide := true})
      refine' ⟨f, h1, h2, h3⟩
    exact Or.inr h_main

lemma round1_h_main_25e071 (R : ℕ)
  (A : Finset ℕ)
  (hA_card : A.card ≥ R + 1):
  ∃ (g : Fin (R + 1) → ℕ), (∀ (i : Fin (R + 1)), g i ∈ A) ∧ (∀ (i j : Fin (R + 1)), i < j → g i < g j) ∧ Function.Injective g := by
  classical
  let l := A.sort (· ≤ ·)
  have h1 : l.length = A.card := by
    simp [l]
  have h2 : l.length ≥ R + 1 := by
    linarith [h1, hA_card]
  let g : Fin (R + 1) → ℕ := fun i => l.get ⟨i.val, by omega⟩
  have h_mem : ∀ (x : ℕ), x ∈ l → x ∈ A := by
    intro x hx
    have h : ∀ (y : ℕ), y ∈ l → y ∈ A := by
      simp [l, Finset.mem_sort]
      <;> tauto
    exact h x hx
  have h3 : ∀ (i : Fin (R + 1)), g i ∈ A := by
    intro i
    have h4 : g i ∈ l := List.get_mem l ⟨i.val, by omega⟩
    exact h_mem (g i) h4
  have h_sorted : l.Sorted (· ≤ ·) := by
    exact Finset.sort_sorted (· ≤ ·) A
  have h_nodup : l.Nodup := Finset.sort_nodup (· ≤ ·) A
  have h4 : ∀ (i j : Fin (R + 1)), i < j → g i < g j := by
    intro i j h
    have h5 : i.val < j.val := by exact_mod_cast h
    have h6 : g i ≤ g j := h_sorted.rel_get_of_lt h5
    have h7 : g i < g j := by
      by_contra h8
      have h9 : g i = g j := by linarith
      have h10 : i.val < j.val := h5
      have h11 : i.val = j.val := by
        have h12 : l.get ⟨i.val, by omega⟩ = l.get ⟨j.val, by omega⟩ := h9
        exact?
      linarith
    exact h7
  have h5 : Function.Injective g := by
    intro i j h
    have h6 : g i = g j := h
    have h7 : i.val = j.val := by
      have h8 : l.get ⟨i.val, by omega⟩ = l.get ⟨j.val, by omega⟩ := h6
      exact?
    apply Fin.ext
    exact h7
  exact ⟨g, h3, h4, h5⟩

theorem round1_pigeonhole_partition_of_neighbors (R1 R2 S : ℕ)
  (hS : S ≥ R1 + R2 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)):
  (∃ (g : Fin (R1 + 1) → ℕ),
    (∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S) ∧
    (∀ (i j : Fin (R1 + 1)), i < j → g i < g j) ∧
    (∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1)) ∨
  (∃ (h : Fin (R2 + 1) → ℕ),
    (∀ (i : Fin (R2 + 1)), 0 < h i ∧ h i ≤ S) ∧
    (∀ (i j : Fin (R2 + 1)), i < j → h i < h j) ∧
    (∀ (i : Fin (R2 + 1)), edge_color 0 (h i) = c2)) := by
  classical
  let A : Finset ℕ := (Finset.Icc 1 S).filter (fun v => edge_color 0 v = c1)
  let B : Finset ℕ := (Finset.Icc 1 S).filter (fun v => edge_color 0 v = c2)
  have h_union : A ∪ B = Finset.Icc 1 S := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    constructor
    ·
      rintro (h | h)
      ·
        rcases h with ⟨h1, _⟩
        exact h1
      ·
        rcases h with ⟨h1, _⟩
        exact h1
    ·
      rintro ⟨h1, h2⟩
      have h3 : 0 < x := by omega
      have h4 : edge_color 0 x = c1 ∨ edge_color 0 x = c2 := h_edge_in_c1_c2 0 x (by omega)
      rcases h4 with (h4 | h4)
      ·
        left
        exact ⟨⟨h1, h2⟩, h4⟩
      ·
        right
        exact ⟨⟨h1, h2⟩, h4⟩
  have h_disj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : edge_color 0 x = c1 := by
      simp only [A, B, Finset.mem_filter] at hx1 <;> tauto
    have h2 : edge_color 0 x = c2 := by
      simp only [A, B, Finset.mem_filter] at hx2 <;> tauto
    have h3 : c1 = c2 := by
      linarith
    exact h_c1_ne_c2 h3
  have h_card : A.card + B.card = (Finset.Icc 1 S).card := by
    rw [← Finset.card_union_of_disjoint h_disj, h_union]
  have h_card2 : (Finset.Icc 1 S).card = S := by
    simp
  have h_main : A.card ≥ R1 + 1 ∨ B.card ≥ R2 + 1 := by
    by_contra h
    push_neg at h
    have h1 : A.card < R1 + 1 := h.1
    have h2 : B.card < R2 + 1 := h.2
    have h3 : A.card + B.card < (R1 + 1) + (R2 + 1) := by omega
    omega
  cases h_main with
  | inl hA =>
    have h_main1 : A.card ≥ R1 + 1 := hA
    have h_exists_g : ∃ (g : Fin (R1 + 1) → ℕ), (∀ (i : Fin (R1 + 1)), g i ∈ A) ∧ (∀ (i j : Fin (R1 + 1)), i < j → g i < g j) ∧ Function.Injective g := round1_h_main_25e071 R1 A h_main1
    rcases h_exists_g with ⟨g, hg1, hg2, _⟩
    have h_g_prop1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S := by
      intro i
      have h4 : g i ∈ A := hg1 i
      have h5 : g i ∈ (Finset.Icc 1 S) := by
        have h6 : g i ∈ A := h4
        have h7 : A ⊆ (Finset.Icc 1 S) := by
          apply Finset.filter_subset
        exact h7 h6
      simp only [Finset.mem_Icc] at h5
      <;> omega
    have h_g_prop2 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1 := by
      intro i
      have h4 : g i ∈ A := hg1 i
      have h5 : g i ∈ (Finset.Icc 1 S) ∧ edge_color 0 (g i) = c1 := by
        simpa [A, Finset.mem_filter] using h4
      exact h5.2
    exact Or.inl ⟨g, h_g_prop1, hg2, h_g_prop2⟩
  | inr hB =>
    have h_main2 : B.card ≥ R2 + 1 := hB
    have h_exists_h : ∃ (h : Fin (R2 + 1) → ℕ), (∀ (i : Fin (R2 + 1)), h i ∈ B) ∧ (∀ (i j : Fin (R2 + 1)), i < j → h i < h j) ∧ Function.Injective h := round1_h_main_25e071 R2 B h_main2
    rcases h_exists_h with ⟨h, hh1, hh2, _⟩
    have h_h_prop1 : ∀ (i : Fin (R2 + 1)), 0 < h i ∧ h i ≤ S := by
      intro i
      have h4 : h i ∈ B := hh1 i
      have h5 : h i ∈ (Finset.Icc 1 S) := by
        have h6 : h i ∈ B := h4
        have h7 : B ⊆ (Finset.Icc 1 S) := by
          apply Finset.filter_subset
        exact h7 h6
      simp only [Finset.mem_Icc] at h5 <;> omega
    have h_h_prop2 : ∀ (i : Fin (R2 + 1)), edge_color 0 (h i) = c2 := by
      intro i
      have h4 : h i ∈ B := hh1 i
      have h5 : h i ∈ (Finset.Icc 1 S) ∧ edge_color 0 (h i) = c2 := by
        simpa [B, Finset.mem_filter] using h4
      exact h5.2
    exact Or.inr ⟨h, h_h_prop1, hh2, h_h_prop2⟩

theorem round1_c2_neighborhood_and_ramsey_s_t_minus_1_implies_goal (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (ht_gt_one : t > 1)
  (R2 : ℕ)
  (h_R2 : ∀ (S2 : ℕ)
    (hS2 : S2 ≥ R2)
    (edge_color2 : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color2 u v = c1 ∨ edge_color2 u v = c2)),
    (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S2) ∧
      (∀ (i j : Fin s), i < j → f i < f j) ∧
      (∀ (i j : Fin s), i < j → edge_color2 (f i) (f j) = c1)) ∨
    (∃ (f : Fin (t - 1) → ℕ), (∀ (i : Fin (t - 1)), f i ≤ S2) ∧
      (∀ (i j : Fin (t - 1)), i < j → f i < f j) ∧
      (∀ (i j : Fin (t - 1)), i < j → edge_color2 (f i) (f j) = c2))):
  ∀ (S : ℕ)
    (hS : S ≥ R2 + 1)
    (edge_color : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
    (h : Fin (R2 + 1) → ℕ)
    (hh1 : ∀ (i : Fin (R2 + 1)), 0 < h i ∧ h i ≤ S)
    (hh2 : ∀ (i j : Fin (R2 + 1)), i < j → h i < h j)
    (hh3 : ∀ (i : Fin (R2 + 1)), edge_color 0 (h i) = c2),
  (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
    (∀ (i j : Fin s), i < j → f i < f j) ∧
    (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
  intro S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 h hh1 hh2 hh3
  let edge_color2 : ℕ → ℕ → ℤ := fun (u v : ℕ) =>
    if h1 : u < R2 + 1 ∧ v < R2 + 1 then edge_color (h ⟨u, h1.1⟩) (h ⟨v, h1.2⟩) else c1
  have h_main_conj : ∀ (u v : ℕ), u < v → (edge_color2 u v = c1 ∨ edge_color2 u v = c2) := by
    intro u v huv
    by_cases h1 : u < R2 + 1 ∧ v < R2 + 1
    ·
      have h2 : (⟨u, h1.1⟩ : Fin (R2 + 1)) < (⟨v, h1.2⟩ : Fin (R2 + 1)) := by
        exact_mod_cast huv
      have h3 : h (⟨u, h1.1⟩ : Fin (R2 + 1)) < h (⟨v, h1.2⟩ : Fin (R2 + 1)) := hh2 _ _ h2
      have h4 : edge_color2 u v = edge_color (h ⟨u, h1.1⟩) (h ⟨v, h1.2⟩) := by
        simp [edge_color2, h1]
      rw [h4]
      exact h_edge_in_c1_c2 (h ⟨u, h1.1⟩) (h ⟨v, h1.2⟩) h3
    ·
      have h2 : edge_color2 u v = c1 := by simp [edge_color2, h1]
      rw [h2]
      exact Or.inl rfl
  have hS2 : R2 ≥ R2 := by linarith
  have h_cases := h_R2 R2 hS2 edge_color2 c1 c2 h_c1_ne_c2 h_main_conj
  cases h_cases with
  | inl h1 =>
    rcases h1 with ⟨f, h_f1, h_f2, h_f3⟩
    refine' Or.inl ⟨fun (i : Fin s) => h (⟨f i, by linarith [h_f1 i]⟩ : Fin (R2 + 1)), ?_, ?_, ?_⟩
    · intro i
      have h4 : f i ≤ R2 := h_f1 i
      have h5 : f i < R2 + 1 := by linarith
      exact (hh1 (⟨f i, h5⟩ : Fin (R2 + 1))).2
    · intro i j hij
      have h6 : f i < f j := h_f2 i j hij
      have h7 : f i < R2 + 1 := by linarith [h_f1 i]
      have h8 : f j < R2 + 1 := by linarith [h_f1 j]
      exact hh2 (⟨f i, h7⟩ : Fin (R2 + 1)) (⟨f j, h8⟩ : Fin (R2 + 1)) h6
    · intro i j hij
      have h7 : f i < R2 + 1 := by linarith [h_f1 i]
      have h8 : f j < R2 + 1 := by linarith [h_f1 j]
      have h9 : edge_color2 (f i) (f j) = edge_color (h (⟨f i, h7⟩ : Fin (R2 + 1))) (h (⟨f j, h8⟩ : Fin (R2 + 1))) := by
        simp [edge_color2, show (f i < R2 + 1 ∧ f j < R2 + 1) from ⟨h7, h8⟩]
      have h10 : edge_color2 (f i) (f j) = c1 := h_f3 i j hij
      rw [h9] at h10
      exact h10
  | inr h2 =>
    rcases h2 with ⟨f, h_f1, h_f2, h_f3⟩
    have h_t_pos : 0 < t := by linarith
    let g : Fin t → ℕ := fun (i : Fin t) =>
      if h_i : i.val = 0 then 0
      else
        let i' : Fin (t - 1) := ⟨i.val - 1, by omega⟩
        h (⟨f i', by linarith [h_f1 i']⟩ : Fin (R2 + 1))
    have h_g1 : ∀ (i : Fin t), g i ≤ S := by
      intro i
      by_cases h_i : i.val = 0
      ·
        simp [g, h_i]
        <;> omega
      ·
        have h_i_pos : 0 < i.val := by omega
        let i' : Fin (t - 1) := ⟨i.val - 1, by omega⟩
        have h11 : g i = h (⟨f i', by linarith [h_f1 i']⟩ : Fin (R2 + 1)) := by
          simp [g, h_i, i'] <;> aesop
        rw [h11]
        exact (hh1 (⟨f i', by linarith [h_f1 i']⟩ : Fin (R2 + 1))).2
    have h_g2 : ∀ (i j : Fin t), i < j → g i < g j := by
      intro i j hij
      by_cases h_i : i.val = 0
      ·
        have h_j_pos : 0 < j.val := by omega
        have h1 : g i = 0 := by simp [g, h_i]
        have h2 : g j = h (⟨f ⟨j.val - 1, by omega⟩, by linarith [h_f1 ⟨j.val - 1, by omega⟩]⟩ : Fin (R2 + 1)) := by
          simp [g, show j.val ≠ 0 from by omega] <;> aesop
        rw [h1, h2]
        have h3 : 0 < h (⟨f ⟨j.val - 1, by omega⟩, by linarith [h_f1 ⟨j.val - 1, by omega⟩]⟩ : Fin (R2 + 1)) :=
          (hh1 _).1
        exact h3
      ·
        have h_i_pos : 0 < i.val := by omega
        have h_j_pos : 0 < j.val := by omega
        let i' : Fin (t - 1) := ⟨i.val - 1, by omega⟩
        let j' : Fin (t - 1) := ⟨j.val - 1, by omega⟩
        have h1 : i' < j' := by
          simp [i', j'] <;> omega
        have h2 : f i' < f j' := h_f2 i' j' h1
        have h3 : g i = h (⟨f i', by linarith [h_f1 i']⟩ : Fin (R2 + 1)) := by
          simp [g, h_i, i'] <;> aesop
        have h4 : g j = h (⟨f j', by linarith [h_f1 j']⟩ : Fin (R2 + 1)) := by
          simp [g, show j.val ≠ 0 from by omega, j'] <;> aesop
        rw [h3, h4]
        exact hh2 (⟨f i', by linarith [h_f1 i']⟩ : Fin (R2 + 1)) (⟨f j', by linarith [h_f1 j']⟩ : Fin (R2 + 1)) h2
    have h_g3 : ∀ (i j : Fin t), i < j → edge_color (g i) (g j) = c2 := by
      intro i j hij
      by_cases h_i : i.val = 0
      ·
        have h_j_pos : 0 < j.val := by omega
        have h1 : g i = 0 := by simp [g, h_i]
        have h2 : g j = h (⟨f ⟨j.val - 1, by omega⟩, by linarith [h_f1 ⟨j.val - 1, by omega⟩]⟩ : Fin (R2 + 1)) := by
          simp [g, show j.val ≠ 0 from by omega] <;> aesop
        rw [h1, h2]
        exact hh3 (⟨f ⟨j.val - 1, by omega⟩, by linarith [h_f1 ⟨j.val - 1, by omega⟩]⟩ : Fin (R2 + 1))
      ·
        have h_i_pos : 0 < i.val := by omega
        have h_j_pos : 0 < j.val := by omega
        let i' : Fin (t - 1) := ⟨i.val - 1, by omega⟩
        let j' : Fin (t - 1) := ⟨j.val - 1, by omega⟩
        have h1 : i' < j' := by
          simp [i', j'] <;> omega
        have h_fi' : f i' < R2 + 1 := by linarith [h_f1 i']
        have h_fj' : f j' < R2 + 1 := by linarith [h_f1 j']
        have h5 : edge_color2 (f i') (f j') = c2 := h_f3 i' j' h1
        have h6 : edge_color2 (f i') (f j') = edge_color (h (⟨f i', h_fi'⟩ : Fin (R2 + 1))) (h (⟨f j', h_fj'⟩ : Fin (R2 + 1))) := by
          simp [edge_color2, show (f i' < R2 + 1 ∧ f j' < R2 + 1) from ⟨h_fi', h_fj'⟩]
        have h7 : edge_color (h (⟨f i', h_fi'⟩ : Fin (R2 + 1))) (h (⟨f j', h_fj'⟩ : Fin (R2 + 1))) = c2 := by
          rw [←h6]
          exact h5
        have h8 : g i = h (⟨f i', h_fi'⟩ : Fin (R2 + 1)) := by
          simp [g, h_i, i'] <;> aesop
        have h9 : g j = h (⟨f j', h_fj'⟩ : Fin (R2 + 1)) := by
          simp [g, show j.val ≠ 0 from by omega, j'] <;> aesop
        rw [h8, h9]
        exact h7
    refine' Or.inr ⟨g, h_g1, h_g2, h_g3⟩

theorem ramsey_base_case_k_1 (h_two_color_ramsey_hyp : ∀ (s t : ℕ)
      (hs : s ≥ 1)
      (ht : t ≥ 1),
      ∃ (R : ℕ), ∀ (S : ℕ)
        (hS : S ≥ R)
        (edge_color : ℕ → ℕ → ℤ)
        (c1 c2 : ℤ)
        (h_c1_ne_c2 : c1 ≠ c2)
        (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
        (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
        (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2))):
  ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℕ)
    (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ 1),
    ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ 1)
      (v : Fin 4 → ℕ),
      (∀ (a : Fin 4), v a ≤ S) ∧
      (∀ (a b : Fin 4), a < b → v a < v b) ∧
      (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
  use 3
  intro S hS edge_color h_edge_color_in_1_to_k
  have h1 : ∀ (u v : ℕ), u < v → edge_color u v = 1 := by
    intro u v huv
    have h2 : 1 ≤ edge_color u v ∧ edge_color u v ≤ 1 := h_edge_color_in_1_to_k u v huv
    omega
  refine' ⟨1, by decide, fun i : Fin 4 => i.val, _⟩
  constructor
  ·
    intro a
    fin_cases a <;> simp_all <;> omega
  constructor
  ·
    intro a b h
    simp_all <;> omega
  ·
    intro a b h
    have h3 : (fun i : Fin 4 => i.val) a < (fun i : Fin 4 => i.val) b := by simp_all <;> omega
    exact h1 ((fun i : Fin 4 => i.val) a) ((fun i : Fin 4 => i.val) b) h3

lemma round1_main_a7449b (h_two_color_ramsey_hyp : ∀ (s t : ℕ)
      (hs : s ≥ 1)
      (ht : t ≥ 1),
      ∃ (R : ℕ), ∀ (S : ℕ)
        (hS : S ≥ R)
        (edge_color : ℕ → ℕ → ℤ)
        (c1 c2 : ℤ)
        (h_c1_ne_c2 : c1 ≠ c2)
        (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
        (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
        (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)))
  (k : ℕ)
  (hk : k ≥ 1)
  (R_k : ℕ)
  (h_R_k_property : ∀ (S : ℕ)
      (hS : S ≥ R_k)
      (edge_color : ℕ → ℕ → ℕ)
      (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
      ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
        (v : Fin 4 → ℕ),
        (∀ (a : Fin 4), v a ≤ S) ∧
        (∀ (a b : Fin 4), a < b → v a < v b) ∧
        (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j)):
  ∃ (R : ℕ), ∀ (S : ℕ)
     (hS : S ≥ R)
     (edge_color : ℕ → ℕ → ℕ)
     (h_edge_color_in_1_to_k_plus_1 : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k + 1),
     (∃ (v : Fin 4 → ℕ),
       (∀ (a : Fin 4), v a ≤ S) ∧
       (∀ (a b : Fin 4), a < b → v a < v b) ∧
       (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = 1)) ∨
     (∃ (f : Fin (R_k + 1) → ℕ),
       (∀ (i : Fin (R_k + 1)), f i ≤ S) ∧
       (∀ (i j : Fin (R_k + 1)), i < j → f i < f j) ∧
       (∀ (i j : Fin (R_k + 1)), i < j → edge_color (f i) (f j) ≥ 2)) := by
  have h₁ : 4 ≥ 1 := by norm_num
  have h₂ : R_k + 1 ≥ 1 := by omega
  obtain ⟨R, hR⟩ := h_two_color_ramsey_hyp 4 (R_k + 1) h₁ h₂
  refine' ⟨R, _⟩
  intro S hS edge_color h_edge_color_in_1_to_k_plus_1
  let edge_color2 : ℕ → ℕ → ℤ := fun u v => if edge_color u v = 1 then (0 : ℤ) else (1 : ℤ)
  have h_edge_in_colors : ∀ (u v : ℕ), u < v → (edge_color2 u v = (0 : ℤ) ∨ edge_color2 u v = (1 : ℤ)) := by
    intro u v huv
    dsimp [edge_color2]
    by_cases h : edge_color u v = 1
    · simp [h]
    · simp [h]
  have h_main : (∃ (f : Fin 4 → ℕ), (∀ (i : Fin 4), f i ≤ S) ∧ (∀ (i j : Fin 4), i < j → f i < f j) ∧ (∀ (i j : Fin 4), i < j → edge_color2 (f i) (f j) = (0 : ℤ))) ∨
                 (∃ (f : Fin (R_k + 1) → ℕ), (∀ (i : Fin (R_k + 1)), f i ≤ S) ∧ (∀ (i j : Fin (R_k + 1)), i < j → f i < f j) ∧ (∀ (i j : Fin (R_k + 1)), i < j → edge_color2 (f i) (f j) = (1 : ℤ))) := by
    have h' := hR S hS edge_color2 (0 : ℤ) (1 : ℤ) (by norm_num) h_edge_in_colors
    exact h'
  cases h_main with
  | inl h_main1 =>
    rcases h_main1 with ⟨v, hv1, hv2, hv3⟩
    left
    refine' ⟨v, hv1, hv2, _⟩
    intro a b hab
    have h₃ : edge_color2 (v a) (v b) = (0 : ℤ) := hv3 a b hab
    have h₅ : edge_color (v a) (v b) = 1 := by
      dsimp [edge_color2] at h₃
      split_ifs at h₃ <;> tauto
    exact h₅
  | inr h_main2 =>
    rcases h_main2 with ⟨f, hf1, hf2, hf3⟩
    right
    refine' ⟨f, hf1, hf2, _⟩
    intro i j hij
    have h_lt : f i < f j := hf2 i j hij
    have h₄ : edge_color2 (f i) (f j) = (1 : ℤ) := hf3 i j hij
    have h₅ : ¬ (edge_color (f i) (f j) = 1) := by
      dsimp [edge_color2] at h₄
      split_ifs at h₄ <;> tauto
    have h₆ : 1 ≤ edge_color (f i) (f j) ∧ edge_color (f i) (f j) ≤ k + 1 := h_edge_color_in_1_to_k_plus_1 (f i) (f j) h_lt
    have h₇ : edge_color (f i) (f j) ≥ 2 := by omega
    exact h₇

theorem ramsey_induction_step_two_color_strategy (h_two_color_ramsey_hyp : ∀ (s t : ℕ)
      (hs : s ≥ 1)
      (ht : t ≥ 1),
      ∃ (R : ℕ), ∀ (S : ℕ)
        (hS : S ≥ R)
        (edge_color : ℕ → ℕ → ℤ)
        (c1 c2 : ℤ)
        (h_c1_ne_c2 : c1 ≠ c2)
        (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
        (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
        (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)))
  (k : ℕ)
  (hk : k ≥ 1)
  (R_k : ℕ)
  (h_R_k_property : ∀ (S : ℕ)
      (hS : S ≥ R_k)
      (edge_color : ℕ → ℕ → ℕ)
      (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
      ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
        (v : Fin 4 → ℕ),
        (∀ (a : Fin 4), v a ≤ S) ∧
        (∀ (a b : Fin 4), a < b → v a < v b) ∧
        (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j)):
  ∃ (R : ℕ), ∀ (S : ℕ)
     (hS : S ≥ R)
     (edge_color : ℕ → ℕ → ℕ)
     (h_edge_color_in_1_to_k_plus_1 : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k + 1),
     (∃ (v : Fin 4 → ℕ),
       (∀ (a : Fin 4), v a ≤ S) ∧
       (∀ (a b : Fin 4), a < b → v a < v b) ∧
       (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = 1)) ∨
     (∃ (f : Fin (R_k + 1) → ℕ),
       (∀ (i : Fin (R_k + 1)), f i ≤ S) ∧
       (∀ (i j : Fin (R_k + 1)), i < j → f i < f j) ∧
       (∀ (i j : Fin (R_k + 1)), i < j → edge_color (f i) (f j) ≥ 2)) := by
  exact round1_main_a7449b h_two_color_ramsey_hyp k hk R_k h_R_k_property

lemma round1_h_main_cb4ab8 (k : ℕ)
  (hk : k ≥ 1)
  (R_k : ℕ)
  (h_R_k_property : ∀ (S : ℕ)
      (hS : S ≥ R_k)
      (edge_color : ℕ → ℕ → ℕ)
      (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
      ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
        (v : Fin 4 → ℕ),
        (∀ (a : Fin 4), v a ≤ S) ∧
        (∀ (a b : Fin 4), a < b → v a < v b) ∧
        (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j))
  (S : ℕ)
  (hS : S ≥ R_k)
  (edge_color : ℕ → ℕ → ℕ)
  (h_edge_color_in_1_to_k_plus_1 : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k + 1)
  (f : Fin (R_k + 1) → ℕ)
  (hf1 : ∀ (i : Fin (R_k + 1)), f i ≤ S)
  (hf2 : ∀ (i j : Fin (R_k + 1)), i < j → f i < f j)
  (hf3 : ∀ (i j : Fin (R_k + 1)), i < j → edge_color (f i) (f j) ≥ 2):
  ∃ (j : ℕ) (h_j_bounds : 2 ≤ j ∧ j ≤ k + 1)
     (v : Fin 4 → ℕ),
     (∀ (a : Fin 4), v a ≤ S) ∧
     (∀ (a b : Fin 4), a < b → v a < v b) ∧
     (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
  let edge_color' : ℕ → ℕ → ℕ := fun u v =>
    if h : u < v ∧ u < R_k + 1 ∧ v < R_k + 1
    then (edge_color (f ⟨u, h.2.1⟩) (f ⟨v, h.2.2⟩) - 1)
    else 1
  have h_edge_color'_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color' u v ∧ edge_color' u v ≤ k := by
    intro u v huv
    by_cases h1 : u < v ∧ u < R_k + 1 ∧ v < R_k + 1
    · have h_u_lt_v : (u < v) := h1.1
      have h_u_ltRK : u < R_k + 1 := h1.2.1
      have h_v_ltRK : v < R_k + 1 := h1.2.2
      let i : Fin (R_k + 1) := ⟨u, h_u_ltRK⟩
      let j : Fin (R_k + 1) := ⟨v, h_v_ltRK⟩
      have h_ij : i < j := h_u_lt_v
      have h41 : f i < f j := hf2 i j h_ij
      have h42 : 1 ≤ edge_color (f i) (f j) ∧ edge_color (f i) (f j) ≤ k + 1 := h_edge_color_in_1_to_k_plus_1 (f i) (f j) h41
      have h43 : edge_color (f i) (f j) ≥ 2 := hf3 i j h_ij
      have h2 : edge_color' u v = edge_color (f i) (f j) - 1 := by
        simp [edge_color', h1, i, j] <;> aesop
      rw [h2]
      omega
    · have h2 : edge_color' u v = 1 := by
        simp [edge_color', h1] <;> aesop
      rw [h2]
      have h4 : 1 ≤ k := by omega
      omega
  have h_main1 := h_R_k_property R_k (by omega) edge_color' h_edge_color'_in_1_to_k
  rcases h_main1 with ⟨j', h_j'_bounds, v, h1, h2, h3⟩
  have h4 : ∀ a : Fin 4, v a < R_k + 1 := by
    intro a
    have h5 : v a ≤ R_k := h1 a
    omega
  let w : Fin 4 → (Fin (R_k + 1)) := fun a => ⟨v a, h4 a⟩
  let j := j' + 1
  let actual_v : Fin 4 → ℕ := fun a => f (w a)
  have h_j_bounds : 2 ≤ j ∧ j ≤ k + 1 := by
    omega
  have h5 : ∀ (a : Fin 4), actual_v a ≤ S := by
    intro a
    exact hf1 (w a)
  have h6 : ∀ (a b : Fin 4), a < b → actual_v a < actual_v b := by
    intro a b h
    have h7 : v a < v b := h2 a b h
    have h8 : w a < w b := by
      simp [w, h7] <;> omega
    exact hf2 (w a) (w b) h8
  have h7 : ∀ (a b : Fin 4), a < b → edge_color (actual_v a) (actual_v b) = j := by
    intro a b h
    have h8 : v a < v b := h2 a b h
    have h9 : (v a < v b ∧ v a < R_k + 1 ∧ v b < R_k + 1) := by
      exact ⟨h8, h4 a, h4 b⟩
    have h10 : edge_color' (v a) (v b) = edge_color (f (w a)) (f (w b)) - 1 := by
      simp [edge_color', h9, w]
      <;> aesop
    have h11 : edge_color' (v a) (v b) = j' := h3 a b h
    have h12 : edge_color (f (w a)) (f (w b)) - 1 = j' := by
      rw [h10] at h11 <;> exact h11
    have h13 : edge_color (f (w a)) (f (w b)) = j' + 1 := by omega
    simpa [actual_v] using h13
  exact ⟨j, h_j_bounds, actual_v, h5, h6, h7⟩

theorem ramsey_large_clique_has_k4_in_colors_ge_2 (h_two_color_ramsey_hyp : ∀ (s t : ℕ)
      (hs : s ≥ 1)
      (ht : t ≥ 1),
      ∃ (R : ℕ), ∀ (S : ℕ)
        (hS : S ≥ R)
        (edge_color : ℕ → ℕ → ℤ)
        (c1 c2 : ℤ)
        (h_c1_ne_c2 : c1 ≠ c2)
        (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
        (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
        (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)))
  (k : ℕ)
  (hk : k ≥ 1)
  (R_k : ℕ)
  (h_R_k_property : ∀ (S : ℕ)
      (hS : S ≥ R_k)
      (edge_color : ℕ → ℕ → ℕ)
      (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
      ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
        (v : Fin 4 → ℕ),
        (∀ (a : Fin 4), v a ≤ S) ∧
        (∀ (a b : Fin 4), a < b → v a < v b) ∧
        (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j))
  (S : ℕ)
  (hS : S ≥ R_k)
  (edge_color : ℕ → ℕ → ℕ)
  (h_edge_color_in_1_to_k_plus_1 : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k + 1)
  (f : Fin (R_k + 1) → ℕ)
  (hf1 : ∀ (i : Fin (R_k + 1)), f i ≤ S)
  (hf2 : ∀ (i j : Fin (R_k + 1)), i < j → f i < f j)
  (hf3 : ∀ (i j : Fin (R_k + 1)), i < j → edge_color (f i) (f j) ≥ 2):
  ∃ (j : ℕ) (h_j_bounds : 2 ≤ j ∧ j ≤ k + 1)
     (v : Fin 4 → ℕ),
     (∀ (a : Fin 4), v a ≤ S) ∧
     (∀ (a b : Fin 4), a < b → v a < v b) ∧
     (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
  exact round1_h_main_cb4ab8 k hk R_k h_R_k_property S hS edge_color h_edge_color_in_1_to_k_plus_1 f hf1 hf2 hf3

theorem construct_induced_coloring_from_g (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (S : ℕ)
  (hS : S ≥ R1 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (hg3 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1):
  ∃ (edge_color1 : ℕ → ℕ → ℤ),
    (∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)) ∧
    (∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
      edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩)) := by
  let edge_color1 : ℕ → ℕ → ℤ := fun (u v : ℕ) =>
    if h : u ≤ R1 ∧ v ≤ R1 ∧ u < v then
      edge_color (g ⟨u, Nat.lt_succ_of_le h.1⟩) (g ⟨v, Nat.lt_succ_of_le h.2.1⟩)
    else
      c1
  use edge_color1
  constructor
  ·
    intro u v huv
    by_cases h : u ≤ R1 ∧ v ≤ R1 ∧ u < v
    ·
      have h' : edge_color1 u v = edge_color (g ⟨u, Nat.lt_succ_of_le h.1⟩) (g ⟨v, Nat.lt_succ_of_le h.2.1⟩) := by
        simp [edge_color1, h]
      rw [h']
      exact h_edge_in_c1_c2 (g ⟨u, Nat.lt_succ_of_le h.1⟩) (g ⟨v, Nat.lt_succ_of_le h.2.1⟩) (by
        apply hg2
        <;> simp [h] <;> tauto)
    ·
      have h' : edge_color1 u v = c1 := by
        simp [edge_color1, h]
      rw [h']
      <;> simp
  ·
    intro i hi j hj h_ij
    have h : i ≤ R1 ∧ j ≤ R1 ∧ i < j := ⟨hi, hj, h_ij⟩
    have h' : edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩) := by
      simp [edge_color1, h]
      <;> tauto
    exact h'

theorem apply_ramsey_to_get_c1_or_c2_clique_in_indices (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (h_R1 : ∀ (S1 : ℕ)
    (hS1 : S1 ≥ R1)
    (edge_color1 : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)),
    (∃ (f : Fin (s - 1) → ℕ), (∀ (i : Fin (s - 1)), f i ≤ S1) ∧
      (∀ (i j : Fin (s - 1)), i < j → f i < f j) ∧
      (∀ (i j : Fin (s - 1)), i < j → edge_color1 (f i) (f j) = c1)) ∨
    (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S1) ∧
      (∀ (i j : Fin t), i < j → f i < f j) ∧
      (∀ (i j : Fin t), i < j → edge_color1 (f i) (f j) = c2)))
  (edge_color1 : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge1_prop1 : ∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)):
  (∃ (f : Fin (s - 1) → ℕ), (∀ (i : Fin (s - 1)), f i ≤ R1) ∧
    (∀ (i j : Fin (s - 1)), i < j → f i < f j) ∧
    (∀ (i j : Fin (s - 1)), i < j → edge_color1 (f i) (f j) = c1)) ∨
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ R1) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color1 (f i) (f j) = c2)) := by
  have h₁ : R1 ≥ R1 := by linarith
  exact h_R1 R1 h₁ edge_color1 c1 c2 h_c1_ne_c2 h_edge1_prop1

lemma round1_f_map_properties (s t : ℕ)
  (hs : s ≥ 1)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (S : ℕ)
  (hS : S ≥ R1 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (hg3 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1)
  (edge_color1 : ℕ → ℕ → ℤ)
  (h_edge_color1_relation : ∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
    edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩))
  (f_prime : Fin (s - 1) → ℕ)
  (h_f_prime_bounded : ∀ (i : Fin (s - 1)), f_prime i ≤ R1)
  (h_f_prime_increasing : ∀ (i j : Fin (s - 1)), i < j → f_prime i < f_prime j)
  (h_f_prime_c1_edges : ∀ (i j : Fin (s - 1)), i < j → edge_color1 (f_prime i) (f_prime j) = c1):
  let f : Fin s → ℕ := fun i =>
    if i.val = 0 then 0 else
      let idx := f_prime ⟨i.val - 1, by omega⟩
      have h_lt : idx < R1 + 1 := by
        have h : idx ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
        omega
      g ⟨idx, h_lt⟩
  (∀ (i : Fin s), f i ≤ S) ∧
  (∀ (i j : Fin s), i < j → f i < f j) ∧
  (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1) := by
  let f : Fin s → ℕ := fun i =>
    if i.val = 0 then 0 else
      let idx := f_prime ⟨i.val - 1, by omega⟩
      have h_lt : idx < R1 + 1 := by
        have h : idx ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
        omega
      g ⟨idx, h_lt⟩
  have h1 : ∀ (i : Fin s), f i ≤ S := by
    intro i
    by_cases h_i0 : i.val = 0
    ·
      have h_fi : f i = 0 := by
        simp [f, h_i0]
      rw [h_fi] <;> omega
    ·
      have h_i_pos : 0 < i.val := by omega
      have h2 : f i = g ⟨f_prime ⟨i.val - 1, by omega⟩, by
          have h : f_prime ⟨i.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
          omega⟩ := by
        simp [f, h_i0, h_i_pos] <;> aesop
      rw [h2]
      have h7 : 0 < g ⟨f_prime ⟨i.val - 1, by omega⟩, by
            have h : f_prime ⟨i.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
            omega⟩ ∧ g ⟨f_prime ⟨i.val - 1, by omega⟩, by
            have h : f_prime ⟨i.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
            omega⟩ ≤ S :=
        hg1 ⟨f_prime ⟨i.val - 1, by omega⟩, by
          have h : f_prime ⟨i.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
          omega⟩
      simpa using h7.2
  have h2 : ∀ (i j : Fin s), i < j → f i < f j := by
    intro i j h_ij
    by_cases h_i0 : i.val = 0
    ·
      have h_j_pos : 0 < j.val := by omega
      have h_fi : f i = 0 := by
        simp [f, h_i0]
      have h_fj : f j = g ⟨f_prime ⟨j.val - 1, by omega⟩, by
          have h : f_prime ⟨j.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨j.val - 1, by omega⟩
          omega⟩ := by
        simp [f, show j.val ≠ 0 by omega] <;> aesop
      rw [h_fi, h_fj]
      have h8 : 0 < g ⟨f_prime ⟨j.val - 1, by omega⟩, by
            have h : f_prime ⟨j.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨j.val - 1, by omega⟩
            omega⟩ := (hg1 ⟨f_prime ⟨j.val - 1, by omega⟩, by
          have h : f_prime ⟨j.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨j.val - 1, by omega⟩
          omega⟩).1
      exact h8
    ·
      have h_i_pos : 0 < i.val := by omega
      have h_j_pos : 0 < j.val := by omega
      have h_i' : ∃ (i' : ℕ), i.val = i' + 1 := by
        refine' ⟨i.val - 1, _⟩ <;> omega
      rcases h_i' with ⟨i', hi'⟩
      have h_j' : ∃ (j' : ℕ), j.val = j' + 1 := by
        refine' ⟨j.val - 1, _⟩ <;> omega
      rcases h_j' with ⟨j', hj'⟩
      have h_i'_lt_j' : i' < j' := by omega
      have h_i'_lt : i' < s - 1 := by omega
      have h_j'_lt : j' < s - 1 := by omega
      let i'' : Fin (s - 1) := ⟨i', h_i'_lt⟩
      let j'' : Fin (s - 1) := ⟨j', h_j'_lt⟩
      have h9 : i'' < j'' := by
        simp [i'', j'', h_i'_lt_j'] <;> omega
      let idx1 : Fin (R1 + 1) := ⟨f_prime i'', by
          have h : f_prime i'' ≤ R1 := h_f_prime_bounded i''
          omega⟩
      let idx2 : Fin (R1 + 1) := ⟨f_prime j'', by
          have h : f_prime j'' ≤ R1 := h_f_prime_bounded j''
          omega⟩
      have h10 : f i = g idx1 := by
        simp [f, hi', i'', idx1, hi'] <;> omega
      have h11 : f j = g idx2 := by
        simp [f, hj', j'', idx2, hj'] <;> omega
      rw [h10, h11]
      have h12 : f_prime i'' < f_prime j'' := h_f_prime_increasing i'' j'' h9
      exact hg2 idx1 idx2 (by simpa [idx1, idx2] using h12)
  have h3 : ∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1 := by
    intro i j h_ij
    by_cases h_i0 : i.val = 0
    ·
      have h_fi : f i = 0 := by
        simp [f, h_i0]
      have h_j_pos : 0 < j.val := by omega
      have h_fj : f j = g ⟨f_prime ⟨j.val - 1, by omega⟩, by
          have h : f_prime ⟨j.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨j.val - 1, by omega⟩
          omega⟩ := by
        simp [f, show j.val ≠ 0 by omega] <;> aesop
      rw [h_fi, h_fj]
      exact hg3 ⟨f_prime ⟨j.val - 1, by omega⟩, by
        have h : f_prime ⟨j.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨j.val - 1, by omega⟩
        omega⟩
    ·
      have h_i_pos : 0 < i.val := by omega
      have h_j_pos : 0 < j.val := by omega
      have h_i' : ∃ (i' : ℕ), i.val = i' + 1 := by
        refine' ⟨i.val - 1, _⟩ <;> omega
      rcases h_i' with ⟨i', hi'⟩
      have h_j' : ∃ (j' : ℕ), j.val = j' + 1 := by
        refine' ⟨j.val - 1, _⟩ <;> omega
      rcases h_j' with ⟨j', hj'⟩
      have h_i'_lt_j' : i' < j' := by omega
      have h_i'_lt : i' < s - 1 := by omega
      have h_j'_lt : j' < s - 1 := by omega
      let i'' : Fin (s - 1) := ⟨i', h_i'_lt⟩
      let j'' : Fin (s - 1) := ⟨j', h_j'_lt⟩
      have h9 : i'' < j'' := by
        simp [i'', j'', h_i'_lt_j'] <;> omega
      let idx1 : Fin (R1 + 1) := ⟨f_prime i'', by
          have h : f_prime i'' ≤ R1 := h_f_prime_bounded i''
          omega⟩
      let idx2 : Fin (R1 + 1) := ⟨f_prime j'', by
          have h : f_prime j'' ≤ R1 := h_f_prime_bounded j''
          omega⟩
      have h10 : f i = g idx1 := by
        simp [f, hi', i'', idx1, hi'] <;> omega
      have h11 : f j = g idx2 := by
        simp [f, hj', j'', idx2, hj'] <;> omega
      rw [h10, h11]
      have h12 : edge_color1 (f_prime i'') (f_prime j'') = c1 := h_f_prime_c1_edges i'' j'' h9
      have h13 : f_prime i'' ≤ R1 := h_f_prime_bounded i''
      have h14 : f_prime j'' ≤ R1 := h_f_prime_bounded j''
      have h15 : edge_color (g idx1) (g idx2) = edge_color1 (f_prime i'') (f_prime j'') := by
        have h16 : edge_color1 (f_prime i'') (f_prime j'') = edge_color (g ⟨f_prime i'', Nat.lt_succ_of_le h13⟩) (g ⟨f_prime j'', Nat.lt_succ_of_le h14⟩) :=
          h_edge_color1_relation (f_prime i'') h13 (f_prime j'') h14 (h_f_prime_increasing i'' j'' h9)
        simpa [idx1, idx2] using h16.symm
      rw [h15, h12]
  exact ⟨h1, h2, h3⟩

theorem c1_clique_s_minus_1_indices_to_s_original (s t : ℕ)
  (hs : s ≥ 1)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (S : ℕ)
  (hS : S ≥ R1 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (hg3 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1)
  (edge_color1 : ℕ → ℕ → ℤ)
  (h_edge_color1_relation : ∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
    edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩))
  (f_prime : Fin (s - 1) → ℕ)
  (h_f_prime_bounded : ∀ (i : Fin (s - 1)), f_prime i ≤ R1)
  (h_f_prime_increasing : ∀ (i j : Fin (s - 1)), i < j → f_prime i < f_prime j)
  (h_f_prime_c1_edges : ∀ (i j : Fin (s - 1)), i < j → edge_color1 (f_prime i) (f_prime j) = c1):
  (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
    (∀ (i j : Fin s), i < j → f i < f j) ∧
    (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) := by
  let f : Fin s → ℕ := fun i =>
    if i.val = 0 then 0 else
      g ⟨f_prime ⟨i.val - 1, by omega⟩, by
        have h : f_prime ⟨i.val - 1, by omega⟩ ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
        omega⟩
  have h_main : (∀ (i : Fin s), f i ≤ S) ∧ (∀ (i j : Fin s), i < j → f i < f j) ∧ (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1) :=
    round1_f_map_properties s t hs hs_gt_one R1 S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 hg3 edge_color1 h_edge_color1_relation f_prime h_f_prime_bounded h_f_prime_increasing h_f_prime_c1_edges
  exact ⟨f, h_main⟩

lemma round1_h_main_7c09e7 (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (R1 : ℕ)
  (S : ℕ)
  (hS : S ≥ R1 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (edge_color1 : ℕ → ℕ → ℤ)
  (h_edge_color1_relation : ∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
    edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩))
  (f_prime : Fin t → ℕ)
  (h_f_prime_bounded : ∀ (i : Fin t), f_prime i ≤ R1)
  (h_f_prime_increasing : ∀ (i j : Fin t), i < j → f_prime i < f_prime j)
  (h_f_prime_c2_edges : ∀ (i j : Fin t), i < j → edge_color1 (f_prime i) (f_prime j) = c2):
  ∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2) := by
  let f : Fin t → ℕ := fun i : Fin t => g ⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩
  have h1 : ∀ (i : Fin t), f i ≤ S := by
    intro i
    have h2 : 0 < g ⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩ ∧ g ⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩ ≤ S :=
      hg1 ⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩
    exact h2.2
  have h3 : ∀ (i j : Fin t), i < j → f i < f j := by
    intro i j h4
    have h5 : f_prime i < f_prime j := h_f_prime_increasing i j h4
    have h6 : (⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩ : Fin (R1 + 1)) <
        (⟨f_prime j, Nat.lt_succ_of_le (h_f_prime_bounded j)⟩ : Fin (R1 + 1)) := by
      simpa [Fin.mk_lt_mk] using h5
    exact hg2 ⟨f_prime i, Nat.lt_succ_of_le (h_f_prime_bounded i)⟩ ⟨f_prime j, Nat.lt_succ_of_le (h_f_prime_bounded j)⟩ h6
  have h4 : ∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2 := by
    intro i j h5
    have h6 : f_prime i ≤ R1 := h_f_prime_bounded i
    have h7 : f_prime j ≤ R1 := h_f_prime_bounded j
    have h8 : f_prime i < f_prime j := h_f_prime_increasing i j h5
    have h10 : edge_color1 (f_prime i) (f_prime j) = edge_color (g ⟨f_prime i, Nat.lt_succ_of_le h6⟩) (g ⟨f_prime j, Nat.lt_succ_of_le h7⟩) :=
      h_edge_color1_relation (f_prime i) h6 (f_prime j) h7 h8
    have h11 : edge_color1 (f_prime i) (f_prime j) = c2 := h_f_prime_c2_edges i j h5
    have h12 : edge_color (g ⟨f_prime i, Nat.lt_succ_of_le h6⟩) (g ⟨f_prime j, Nat.lt_succ_of_le h7⟩) = c2 := by
      rw [←h10, h11]
    simpa [f] using h12
  exact ⟨f, h1, h3, h4⟩

theorem c2_clique_t_indices_to_t_original (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (R1 : ℕ)
  (S : ℕ)
  (hS : S ≥ R1 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (edge_color1 : ℕ → ℕ → ℤ)
  (h_edge_color1_relation : ∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
    edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩))
  (f_prime : Fin t → ℕ)
  (h_f_prime_bounded : ∀ (i : Fin t), f_prime i ≤ R1)
  (h_f_prime_increasing : ∀ (i j : Fin t), i < j → f_prime i < f_prime j)
  (h_f_prime_c2_edges : ∀ (i j : Fin t), i < j → edge_color1 (f_prime i) (f_prime j) = c2):
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
  exact round1_h_main_7c09e7 s t hs ht R1 S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 edge_color1 h_edge_color1_relation f_prime h_f_prime_bounded h_f_prime_increasing h_f_prime_c2_edges

theorem verify_parametric_solution_is_distinct_and_satisfies_equation (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (hne : y ≠ z):
  (k * y * z : ℤ) ≠ 0 ∧
  (k * z * (y + z) : ℤ) ≠ 0 ∧
  (k * y * (y + z) : ℤ) ≠ 0 ∧
  (k * y * z : ℤ) ≠ (k * z * (y + z) : ℤ) ∧
  (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) ∧
  (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) ∧
  (1 / ((k * y * z : ℤ) : ℝ)) = (1 / ((k * z * (y + z) : ℤ) : ℝ)) + (1 / ((k * y * (y + z) : ℤ) : ℝ)) := by
  have h1 : (k * y * z : ℤ) ≠ 0 := by
    exact product_k_y_z_is_nonzero k y z hk hy hz
  have h2 : (k * z * (y + z) : ℤ) ≠ 0 := by
    exact product_k_z_y_add_z_is_nonzero k y z hk hy hz
  have h3 : (k * y * (y + z) : ℤ) ≠ 0 := by
    exact product_k_y_y_add_z_is_nonzero k y z hk hy hz
  have h4 : (k * y * z : ℤ) ≠ (k * z * (y + z) : ℤ) := by
    exact product_k_y_z_ne_product_k_z_y_add_z k y z hk hy hz hne
  have h5 : (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) := by
    exact product_k_z_y_add_z_ne_product_k_y_y_add_z k y z hk hy hz hne
  have h6 : (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) := by
    exact product_k_y_z_ne_product_k_y_y_add_z k y z hk hy hz hne
  have h7 : (1 / ((k * y * z : ℤ) : ℝ)) = (1 / ((k * z * (y + z) : ℤ) : ℝ)) + (1 / ((k * y * (y + z) : ℤ) : ℝ)) := by
    exact reciprocal_relation_of_parametric_products k y z hk hy hz h1 h2 h3
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem transfer_monochromatic_property_from_natural_to_integer (𝓒 : ℤ → ℤ)
  (χ : ℕ → ℤ)
  (h_χ : ∀ (n : ℕ), χ n = 𝓒 (n : ℤ))
  (k y z : ℕ)
  (hk : k ≥ 1)
  (hy : y ≥ 1)
  (hz : z ≥ 1)
  (h_monochromatic : χ (k * y * z) = χ (k * z * (y + z)) ∧ χ (k * z * (y + z)) = χ (k * y * (y + z))):
  (𝓒 '' {((k * y * z : ℕ) : ℤ), ((k * z * (y + z) : ℕ) : ℤ), ((k * y * (y + z) : ℕ) : ℤ)}).Subsingleton := by
  have h1 : 𝓒 ((k * y * z : ℕ) : ℤ) = 𝓒 ((k * z * (y + z) : ℕ) : ℤ) ∧ 𝓒 ((k * z * (y + z) : ℕ) : ℤ) = 𝓒 ((k * y * (y + z) : ℕ) : ℤ) := by
    exact C_colors_are_equal_from_monochromatic_chi 𝓒 χ h_χ k y z hk hy hz h_monochromatic
  set v : ℤ := 𝓒 ((k * y * z : ℕ) : ℤ) with hv_def
  have h11 : 𝓒 ((k * y * z : ℕ) : ℤ) = v := by rfl
  have h12 : 𝓒 ((k * z * (y + z) : ℕ) : ℤ) = v := by
    linarith [h1.1]
  have h13 : 𝓒 ((k * y * (y + z) : ℕ) : ℤ) = v := by
    linarith [h1.1, h1.2]
  have h2 : 𝓒 '' {((k * y * z : ℕ) : ℤ), ((k * z * (y + z) : ℕ) : ℤ), ((k * y * (y + z) : ℕ) : ℤ)} = {v} := by
    exact image_of_three_integers_with_same_color_is_singleton_set 𝓒 ((k * y * z : ℕ) : ℤ) ((k * z * (y + z) : ℕ) : ℤ) ((k * y * (y + z) : ℕ) : ℤ) v h11 h12 h13
  have h3 : (𝓒 '' {((k * y * z : ℕ) : ℤ), ((k * z * (y + z) : ℕ) : ℤ), ((k * y * (y + z) : ℕ) : ℤ)}).Subsingleton := by
    exact a_singleton_set_is_subsingleton v _ h2
  exact h3

theorem schur_triple_produces_unit_fraction_solution (χ : ℕ → ℤ)
  (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_ne : u ≠ v)
  (h_lt1 : u < v)
  (h_lt2 : u + v < N)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N)
  (hsum_dvd_N : (u + v) ∣ N)
  (h_color : χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v))):
  ∃ (A B C : ℕ),
    A ≥ 1 ∧ B ≥ 1 ∧ C ≥ 1 ∧ B ≠ C ∧
    A * (B + C) = B * C ∧
    χ A = χ B ∧ χ B = χ C := by
  have h1 : N / u ≥ 1 ∧ N / v ≥ 1 ∧ N / (u + v) ≥ 1 := by
    exact positivity_of_N_div_u_N_div_v_N_div_u_plus_v N u v hN hu hv hu_dvd_N hv_dvd_N hsum_dvd_N
  have h2 : N / u ≠ N / v := by
    exact distinctness_of_N_div_u_and_N_div_v N u v hN hu hv h_ne h_lt1 hu_dvd_N hv_dvd_N
  have h3 : (N / (u + v)) * ((N / u) + (N / v)) = (N / u) * (N / v) := by
    exact algebraic_identity_for_N_div_candidates N u v hN hu hv hu_dvd_N hv_dvd_N hsum_dvd_N
  have h4 : χ (N / (u + v)) = χ (N / u) ∧ χ (N / u) = χ (N / v) := by
    exact coloring_A_B_C_from_hypothesis χ N u v h_color
  have h11 : N / (u + v) ≥ 1 := h1.2.2
  have h12 : N / u ≥ 1 := h1.1
  have h13 : N / v ≥ 1 := h1.2.1
  have h41 : χ (N / (u + v)) = χ (N / u) := h4.1
  have h42 : χ (N / u) = χ (N / v) := h4.2
  refine' ⟨N / (u + v), N / u, N / v, _⟩
  have h2' : N / u ≠ N / v := h2
  exact ⟨h11, h12, h13, h2', h3, h41, h42⟩

theorem u_is_square_from_coprime_product_square (u v s : ℕ)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_coprime : Nat.gcd u v = 1)
  (h_prod : u * v = s^2)
  (h_gcd_mul_distributive : ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b)
  (h_gcd_of_squares : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2):
  (Nat.gcd u s)^2 = u := by
  have h1 : (Nat.gcd u s)^2 = Nat.gcd (u^2) (s^2) := by
    exact gcd_sq_eq_gcd_of_squares u s h_gcd_of_squares
  have h2 : Nat.gcd (u^2) (s^2) = Nat.gcd (u^2) (u * v) := by
    exact gcd_u2_s2_eq_gcd_u2_uv u v s h_prod
  have h3 : Nat.gcd (u^2) (u * v) = u * Nat.gcd u v := by
    exact gcd_u2_uv_eq_u_gcd_u_v u v hu h_gcd_mul_distributive
  have h4 : (Nat.gcd u s)^2 = u * Nat.gcd u v := by
    rw [h1, h2, h3]
  have h5 : u * Nat.gcd u v = u := by
    rw [h_coprime]
    <;> simp [mul_one]
  rw [h4, h5]

theorem v_is_square_from_coprime_product_square (u v s : ℕ)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_coprime : Nat.gcd u v = 1)
  (h_prod : u * v = s^2)
  (h_gcd_mul_distributive : ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b)
  (h_gcd_of_squares : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2):
  (Nat.gcd v s)^2 = v := by
  have h1 : (Nat.gcd v s)^2 = Nat.gcd (v^2) (s^2) := by
    exact square_gcd_v_s_is_gcd_v2_s2 v s h_gcd_of_squares
  have h2 : Nat.gcd (v^2) (s^2) = Nat.gcd (v^2) (u * v) := by
    exact gcd_v2_s2_eq_gcd_v2_uv_from_prod u v s h_prod
  have h3 : Nat.gcd (v^2) (u * v) = v * Nat.gcd v u := by
    exact gcd_v2_uv_eq_v_mul_gcd_v_u u v h_gcd_mul_distributive
  have h4 : v * Nat.gcd v u = v * Nat.gcd u v := by
    exact v_mul_gcd_v_u_eq_v_mul_gcd_u_v u v
  have h5 : v * Nat.gcd u v = v := by
    exact v_mul_gcd_u_v_eq_v_of_coprime u v h_coprime hv
  rw [h1, h2, h3, h4, h5]

theorem product_is_square_if_gcd_divides_A (U V A : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (hA : A ≥ 1)
  (h_prod : U * V = A^2)
  (u' v' : ℕ)
  (h1 : (Nat.gcd U V) * u' = U)
  (h2 : (Nat.gcd U V) * v' = V)
  (h_gcd_dvd_A : (Nat.gcd U V) ∣ A):
  ∃ s : ℕ, u' * v' = s^2 := by
  have h3 : Nat.gcd U V ≥ 1 := by
    exact lemma_gcd_ge_one U V hU hV
  have h4 : ∃ s : ℕ, A = (Nat.gcd U V) * s := by
    exact lemma_A_eq_gcd_mul_s A (Nat.gcd U V) h_gcd_dvd_A
  rcases h4 with ⟨s, h4⟩
  have h51 : U * V = (Nat.gcd U V) ^ 2 * (u' * v') := by
    calc
      U * V = ((Nat.gcd U V) * u') * ((Nat.gcd U V) * v') := by rw [h1, h2]
      _ = (Nat.gcd U V) ^ 2 * (u' * v') := by ring
  have h52 : A ^ 2 = (Nat.gcd U V) ^ 2 * s ^ 2 := by
    calc
      A ^ 2 = ((Nat.gcd U V) * s) ^ 2 := by rw [h4]
      _ = (Nat.gcd U V) ^ 2 * s ^ 2 := by ring
  have h5 : (Nat.gcd U V) ^ 2 * (u' * v') = (Nat.gcd U V) ^ 2 * s ^ 2 := by
    nlinarith [h_prod, h51, h52]
  have h6 : (Nat.gcd U V) ^ 2 ≠ 0 := by
    have h61 : Nat.gcd U V ≥ 1 := h3
    have h62 : (Nat.gcd U V) ^ 2 ≥ 1 := by
      nlinarith
    have h63 : (Nat.gcd U V) ^ 2 ≠ 0 := by
      omega
    tauto
  have h7 : u' * v' = s ^ 2 := by
    exact lemma_cancel_eq_from_mul_eq u' v' s (Nat.gcd U V) h6 h5
  exact ⟨s, h7⟩

theorem natural_k_color_ramsey_from_two_color_with_le_S (h_two_color_ramsey_hyp : ∀ (s t : ℕ)
      (hs : s ≥ 1)
      (ht : t ≥ 1),
      ∃ (R : ℕ), ∀ (S : ℕ)
        (hS : S ≥ R)
        (edge_color : ℕ → ℕ → ℤ)
        (c1 c2 : ℤ)
        (h_c1_ne_c2 : c1 ≠ c2)
        (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
        (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
        (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)))
  (k : ℕ)
  (hk : k ≥ 1):
  ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℕ)
    (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
    ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
      (v : Fin 4 → ℕ),
      (∀ (a : Fin 4), v a ≤ S) ∧
      (∀ (a b : Fin 4), a < b → v a < v b) ∧
      (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
  have h : ∀ (n : ℕ), n ≥ 1 → ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℕ)
    (h_edge_color_in_1_to_n : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ n),
    ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ n)
      (v : Fin 4 → ℕ),
      (∀ (a : Fin 4), v a ≤ S) ∧
      (∀ (a b : Fin 4), a < b → v a < v b) ∧
      (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      by_cases h1 : n = 0
      ·
        subst h1
        have h_base := ramsey_base_case_k_1 h_two_color_ramsey_hyp
        simpa using h_base
      ·
        have h2 : n ≥ 1 := by
          omega
        have ih' := ih h2
        rcases ih' with ⟨R_n, hR_n⟩
        have h3 : ∃ (R1 : ℕ), ∀ (S : ℕ)
          (hS : S ≥ R1)
          (edge_color : ℕ → ℕ → ℕ)
          (h_edge_color_in_1_to_n_plus_1 : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ n + 1),
          (∃ (v : Fin 4 → ℕ),
            (∀ (a : Fin 4), v a ≤ S) ∧
            (∀ (a b : Fin 4), a < b → v a < v b) ∧
            (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = 1)) ∨
          (∃ (f : Fin (R_n + 1) → ℕ),
            (∀ (i : Fin (R_n + 1)), f i ≤ S) ∧
            (∀ (i j : Fin (R_n + 1)), i < j → f i < f j) ∧
            (∀ (i j : Fin (R_n + 1)), i < j → edge_color (f i) (f j) ≥ 2)) := by
          exact ramsey_induction_step_two_color_strategy h_two_color_ramsey_hyp n h2 R_n hR_n
        rcases h3 with ⟨R1, hR1⟩
        set R := max R1 R_n with hR_def
        use R
        intro S hS edge_color h_edge_color_in_1_to_n_plus_1
        have hS1 : S ≥ R1 := by
          have hR1_le_R : R1 ≤ R := by
            apply le_max_left
          linarith
        have hS2 : S ≥ R_n := by
          have hRn_le_R : R_n ≤ R := by
            apply le_max_right
          linarith
        have h4 : (∃ (v : Fin 4 → ℕ),
          (∀ (a : Fin 4), v a ≤ S) ∧
          (∀ (a b : Fin 4), a < b → v a < v b) ∧
          (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = 1)) ∨
          (∃ (f : Fin (R_n + 1) → ℕ),
            (∀ (i : Fin (R_n + 1)), f i ≤ S) ∧
            (∀ (i j : Fin (R_n + 1)), i < j → f i < f j) ∧
            (∀ (i j : Fin (R_n + 1)), i < j → edge_color (f i) (f j) ≥ 2)) := by
          exact hR1 S hS1 edge_color h_edge_color_in_1_to_n_plus_1
        cases h4 with
        | inl h41 =>
          rcases h41 with ⟨v, hv1, hv2, hv3⟩
          refine' ⟨1, ⟨by norm_num, by omega⟩, v, hv1, hv2, _⟩
          simpa using hv3
        | inr h42 =>
          rcases h42 with ⟨f, hf1, hf2, hf3⟩
          have h5 : ∃ (j : ℕ) (h_j_bounds : 2 ≤ j ∧ j ≤ n + 1)
            (v : Fin 4 → ℕ),
            (∀ (a : Fin 4), v a ≤ S) ∧
            (∀ (a b : Fin 4), a < b → v a < v b) ∧
            (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
            exact ramsey_large_clique_has_k4_in_colors_ge_2 h_two_color_ramsey_hyp n h2 R_n hR_n S hS2 edge_color h_edge_color_in_1_to_n_plus_1 f hf1 hf2 hf3
          rcases h5 with ⟨j, ⟨h_j_ge_2, h_j_le_n_plus_1⟩, v, hv1, hv2, hv3⟩
          refine' ⟨j, ⟨by linarith, by linarith⟩, v, hv1, hv2, hv3⟩
  exact h k hk

theorem round1_c1_neighborhood_and_ramsey_s_minus_1_t_implies_goal (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (h_R1 : ∀ (S1 : ℕ)
    (hS1 : S1 ≥ R1)
    (edge_color1 : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)),
    (∃ (f : Fin (s - 1) → ℕ), (∀ (i : Fin (s - 1)), f i ≤ S1) ∧
      (∀ (i j : Fin (s - 1)), i < j → f i < f j) ∧
      (∀ (i j : Fin (s - 1)), i < j → edge_color1 (f i) (f j) = c1)) ∨
    (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S1) ∧
      (∀ (i j : Fin t), i < j → f i < f j) ∧
      (∀ (i j : Fin t), i < j → edge_color1 (f i) (f j) = c2))):
  ∀ (S : ℕ)
    (hS : S ≥ R1 + 1)
    (edge_color : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
    (g : Fin (R1 + 1) → ℕ)
    (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
    (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
    (hg3 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1),
  (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
    (∀ (i j : Fin s), i < j → f i < f j) ∧
    (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
  intros S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 hg3
  have h1 : ∃ (edge_color1 : ℕ → ℕ → ℤ),
    (∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)) ∧
    (∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
      edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩)) := by
    exact construct_induced_coloring_from_g s t hs ht hs_gt_one R1 S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 hg3
  rcases h1 with ⟨edge_color1, h11, h12⟩
  have h4 : (∃ (f : Fin (s - 1) → ℕ), (∀ (i : Fin (s - 1)), f i ≤ R1) ∧
    (∀ (i j : Fin (s - 1)), i < j → f i < f j) ∧
    (∀ (i j : Fin (s - 1)), i < j → edge_color1 (f i) (f j) = c1)) ∨
    (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ R1) ∧
      (∀ (i j : Fin t), i < j → f i < f j) ∧
      (∀ (i j : Fin t), i < j → edge_color1 (f i) (f j) = c2)) := by
    exact apply_ramsey_to_get_c1_or_c2_clique_in_indices s t hs ht hs_gt_one R1 h_R1 edge_color1 c1 c2 h_c1_ne_c2 h11
  cases h4 with
  | inl h41 =>
    rcases h41 with ⟨f_prime, h_f_prime_bounded, h_f_prime_increasing, h_f_prime_c1_edges⟩
    have h5 : (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
      (∀ (i j : Fin s), i < j → f i < f j) ∧
      (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) := by
      exact c1_clique_s_minus_1_indices_to_s_original s t hs hs_gt_one R1 S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 hg3 edge_color1 h12 f_prime h_f_prime_bounded h_f_prime_increasing h_f_prime_c1_edges
    left
    exact h5
  | inr h42 =>
    rcases h42 with ⟨f_prime, h_f_prime_bounded, h_f_prime_increasing, h_f_prime_c2_edges⟩
    have h6 : (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
      (∀ (i j : Fin t), i < j → f i < f j) ∧
      (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
      exact c2_clique_t_indices_to_t_original s t hs ht R1 S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 edge_color1 h12 f_prime h_f_prime_bounded h_f_prime_increasing h_f_prime_c2_edges
    right
    exact h6

theorem coprime_product_square_implies_both_are_squares (u v : ℕ)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_coprime : Nat.gcd u v = 1)
  (h_prod_is_square : ∃ s : ℕ, u * v = s^2):
  ∃ y z : ℕ, y ≥ 1 ∧ z ≥ 1 ∧ u = y^2 ∧ v = z^2 := by
  rcases h_prod_is_square with ⟨s, h_prod⟩
  have h1 : ∀ (k a b : ℕ), Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
    exact gcd_mul_distributive
  have h2 : ∀ (a b : ℕ), Nat.gcd (a^2) (b^2) = (Nat.gcd a b)^2 := by
    exact gcd_of_squares_is_square_of_gcd
  have h_u_sq : (Nat.gcd u s)^2 = u := by
    exact u_is_square_from_coprime_product_square u v s hu hv h_coprime h_prod h1 h2
  have h_v_sq : (Nat.gcd v s)^2 = v := by
    exact v_is_square_from_coprime_product_square u v s hu hv h_coprime h_prod h1 h2
  have h_u_gcd_pos : Nat.gcd u s ≥ 1 := by
    exact gcd_is_positive_of_square_eq u s hu h_u_sq
  have h_v_gcd_pos : Nat.gcd v s ≥ 1 := by
    exact gcd_is_positive_of_square_eq v s hv h_v_sq
  refine' ⟨Nat.gcd u s, Nat.gcd v s, h_u_gcd_pos, h_v_gcd_pos, _ , _⟩
  ·
    linarith
  ·
    linarith

theorem existence_of_coprime_factors_after_gcd (U V A : ℕ)
  (hU : U ≥ 1)
  (hV : V ≥ 1)
  (hA : A ≥ 1)
  (h_prod : U * V = A^2):
  ∃ u' v' : ℕ,
    u' ≥ 1 ∧
    v' ≥ 1 ∧
    (Nat.gcd U V) * u' = U ∧
    (Nat.gcd U V) * v' = V ∧
    Nat.gcd u' v' = 1 ∧
    (∃ s : ℕ, u' * v' = s^2) := by
  rcases existence_of_u_prime_v_prime U V hU hV with ⟨u', v', h_u'_ge_1, h_v'_ge_1, h_gcd_mul_u'_eq_U, h_gcd_mul_v'_eq_V⟩
  have h_coprime : Nat.gcd u' v' = 1 := by
    exact coprime_after_division_by_gcd U V hU hV u' v' h_gcd_mul_u'_eq_U h_gcd_mul_v'_eq_V
  have h_gcd_sq_dvd_A_sq : (Nat.gcd U V) ^ 2 ∣ A ^ 2 := by
    exact gcd_sq_divides_A_sq U V A hU hV hA h_prod u' v' h_gcd_mul_u'_eq_U h_gcd_mul_v'_eq_V
  have h_gcd_dvd_A : (Nat.gcd U V) ∣ A := by
    exact square_divides_square_implies_divides (Nat.gcd U V) A h_gcd_sq_dvd_A_sq
  have h_exists_s : ∃ s : ℕ, u' * v' = s ^ 2 := by
    exact product_is_square_if_gcd_divides_A U V A hU hV hA h_prod u' v' h_gcd_mul_u'_eq_U h_gcd_mul_v'_eq_V h_gcd_dvd_A
  exact ⟨u', v', h_u'_ge_1, h_v'_ge_1, h_gcd_mul_u'_eq_U, h_gcd_mul_v'_eq_V, h_coprime, h_exists_s⟩

theorem ramsey_two_color_general_with_le_S (s t : ℕ)
  (hs : s ≥ 1)
  (ht : t ≥ 1):
  ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℤ)
    (c1 c2 : ℤ)
    (h_c1_ne_c2 : c1 ≠ c2)
    (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
  (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
    (∀ (i j : Fin s), i < j → f i < f j) ∧
    (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
  (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
    (∀ (i j : Fin t), i < j → f i < f j) ∧
    (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
  have h : ∀ (k : ℕ), ∀ (s t : ℕ), s ≥ 1 → t ≥ 1 → s + t = k →
    (∃ (R : ℕ), ∀ (S : ℕ)
      (hS : S ≥ R)
      (edge_color : ℕ → ℕ → ℤ)
      (c1 c2 : ℤ)
      (h_c1_ne_c2 : c1 ≠ c2)
      (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
      (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
        (∀ (i j : Fin s), i < j → f i < f j) ∧
        (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
      (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
        (∀ (i j : Fin t), i < j → f i < f j) ∧
        (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro s t hs ht h_sum
      by_cases h1 : s = 1 ∨ t = 1
      ·
        exact round1_ramsey_base_case_s_or_t_eq_1 s t hs ht h1
      ·
        have hs_gt_one : s > 1 := by
          by_contra h2
          have h21 : s ≤ 1 := by linarith
          have h22 : s ≥ 1 := hs
          have h23 : s = 1 := by omega
          have h11 : s = 1 ∨ t = 1 := Or.inl h23
          tauto
        have ht_gt_one : t > 1 := by
          by_contra h2
          have h21 : t ≤ 1 := by linarith
          have h22 : t ≥ 1 := ht
          have h23 : t = 1 := by omega
          have h11 : s = 1 ∨ t = 1 := Or.inr h23
          tauto
        have h2 : (s - 1) + t < k := by
          omega
        have h3 : s + (t - 1) < k := by
          omega
        have h4 : ∃ (R1 : ℕ), ∀ (S1 : ℕ)
          (hS1 : S1 ≥ R1)
          (edge_color1 : ℕ → ℕ → ℤ)
          (c1 c2 : ℤ)
          (h_c1_ne_c2 : c1 ≠ c2)
          (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)),
          (∃ (f : Fin (s - 1) → ℕ), (∀ (i : Fin (s - 1)), f i ≤ S1) ∧
            (∀ (i j : Fin (s - 1)), i < j → f i < f j) ∧
            (∀ (i j : Fin (s - 1)), i < j → edge_color1 (f i) (f j) = c1)) ∨
          (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S1) ∧
            (∀ (i j : Fin t), i < j → f i < f j) ∧
            (∀ (i j : Fin t), i < j → edge_color1 (f i) (f j) = c2)) := by
          have h41 := ih ((s - 1) + t) h2 (s - 1) t (by hint) (by omega) (by omega)
          simpa using h41
        have h5 : ∃ (R2 : ℕ), ∀ (S2 : ℕ)
          (hS2 : S2 ≥ R2)
          (edge_color2 : ℕ → ℕ → ℤ)
          (c1 c2 : ℤ)
          (h_c1_ne_c2 : c1 ≠ c2)
          (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color2 u v = c1 ∨ edge_color2 u v = c2)),
          (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S2) ∧
            (∀ (i j : Fin s), i < j → f i < f j) ∧
            (∀ (i j : Fin s), i < j → edge_color2 (f i) (f j) = c1)) ∨
          (∃ (f : Fin (t - 1) → ℕ), (∀ (i : Fin (t - 1)), f i ≤ S2) ∧
            (∀ (i j : Fin (t - 1)), i < j → f i < f j) ∧
            (∀ (i j : Fin (t - 1)), i < j → edge_color2 (f i) (f j) = c2)) := by
          have h51 := ih (s + (t - 1)) h3 s (t - 1) (by omega) (by omega) (by omega)
          simpa using h51
        rcases h4 with ⟨R1, h_R1⟩
        rcases h5 with ⟨R2, h_R2⟩
        use R1 + R2 + 1
        intro S hS edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2
        have hS1 : S ≥ R1 + R2 + 1 := hS
        have h6 := round1_pigeonhole_partition_of_neighbors R1 R2 S hS1 edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2
        rcases h6 with (h61 | h62)
        ·
          rcases h61 with ⟨g, hg1, hg2, hg3⟩
          have h7 := round1_c1_neighborhood_and_ramsey_s_minus_1_t_implies_goal s t hs ht hs_gt_one R1 h_R1 S (by omega) edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 g hg1 hg2 hg3
          tauto
        ·
          rcases h62 with ⟨h_func, hh1, hh2, hh3⟩
          have h7 := round1_c2_neighborhood_and_ramsey_s_t_minus_1_implies_goal s t hs ht ht_gt_one R2 h_R2 S (by omega) edge_color c1 c2 h_c1_ne_c2 h_edge_in_c1_c2 h_func hh1 hh2 hh3
          tauto
  have h6 := h (s + t) s t hs ht (by hint)
  simpa using h6

theorem unit_fraction_solution_has_parametric_form (A B C : ℕ)
  (hA : A ≥ 1)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_ne : B ≠ C)
  (h_eq : A * (B + C) = B * C):
  ∃ (k y z : ℕ),
    k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧
    A = k * y * z ∧
    ((B = k * z * (y + z) ∧ C = k * y * (y + z)) ∨ (B = k * y * (y + z) ∧ C = k * z * (y + z))) := by
  have h1 : B > A ∧ C > A ∧ (B - A) * (C - A) = A^2 := by
    exact algebraic_manipulation_inequality_and_product A B C hA hB hC h_eq
  have h11 : B > A := h1.1
  have h12 : C > A := h1.2.1
  have h13 : (B - A) * (C - A) = A^2 := h1.2.2
  set U : ℕ := B - A with hU_def
  set V : ℕ := C - A with hV_def
  have hU : U ≥ 1 := by omega
  have hV : V ≥ 1 := by omega
  have h_prod : U * V = A^2 := by
    simpa [hU_def, hV_def] using h13
  have h21 : ∃ u' v' : ℕ,
    u' ≥ 1 ∧
    v' ≥ 1 ∧
    (Nat.gcd U V) * u' = U ∧
    (Nat.gcd U V) * v' = V ∧
    Nat.gcd u' v' = 1 ∧
    (∃ s : ℕ, u' * v' = s^2) := by
    exact existence_of_coprime_factors_after_gcd U V A hU hV hA h_prod
  rcases h21 with ⟨u', v', hu', hv', h4, h5, h6, h7⟩
  have h22 : ∃ y z : ℕ, y ≥ 1 ∧ z ≥ 1 ∧ u' = y^2 ∧ v' = z^2 := by
    exact coprime_product_square_implies_both_are_squares u' v' hu' hv' h6 h7
  rcases h22 with ⟨y, z, hy, hz, h_u_eq_y2, h_v_eq_z2⟩
  set k : ℕ := Nat.gcd U V with hk_def
  have h41 : k * u' = U := by
    linarith
  have h42 : k * v' = V := by
    linarith
  have h411 : k * y^2 = U := by
    have h412 : u' = y^2 := h_u_eq_y2
    rw [h412] at h41
    linarith
  have h422 : k * z^2 = V := by
    have h423 : v' = z^2 := h_v_eq_z2
    rw [h423] at h42
    linarith
  have hk_ge_1 : k ≥ 1 := by
    by_contra h
    have h_k0 : k = 0 := by omega
    rw [h_k0] at h41
    have h413 : U = 0 := by nlinarith
    omega
  have h_A : A = k * y * z := by
    have h101 : (k * y * z) ^ 2 = A ^ 2 := by
      have h102 : (k * y * z) ^ 2 = (k ^ 2) * (y ^ 2 * z ^ 2) := by
        ring
      have h103 : (k * y ^ 2) * (k * z ^ 2) = A ^ 2 := by
        have h104 : (k * y ^ 2) = U := by linarith
        have h105 : (k * z ^ 2) = V := by linarith
        have h106 : U * V = A ^ 2 := h_prod
        rw [h104, h105] at *
        <;> nlinarith
      have h107 : (k ^ 2) * (y ^ 2 * z ^ 2) = (k * y ^ 2) * (k * z ^ 2) := by
        ring
      linarith
    have h108 : k * y * z ≥ 0 := by positivity
    have h109 : A ≥ 0 := by positivity
    nlinarith [sq_nonneg (k * y * z), sq_nonneg A]
  have hB_eq : B = A + k * y^2 := by
    have hU_def1 : U = B - A := by omega
    have h414 : k * y^2 = U := by linarith
    omega
  have hC_eq : C = A + k * z^2 := by
    have hV_def1 : V = C - A := by omega
    have h423 : k * z^2 = V := by linarith
    omega
  have hB_eq2 : B = k * y * (y + z) := by
    have h101 : B = A + k * y^2 := hB_eq
    have h102 : A = k * y * z := h_A
    rw [h101, h102]
    <;> ring_nf <;> hint
  have hC_eq2 : C = k * z * (y + z) := by
    have h101 : C = A + k * z^2 := hC_eq
    have h102 : A = k * y * z := h_A
    rw [h101, h102]
    <;> ring_nf <;> hint
  have h_y_ne_z : y ≠ z := by
    by_contra h_yz_eq
    have h_U_eq_V : U = V := by
      have h1 : k * y^2 = U := by linarith
      have h2 : k * z^2 = V := by linarith
      have h3 : y = z := by tauto
      have h4 : k * y^2 = k * z^2 := by
        rw [h3]
        <;> ring
      linarith
    have h_B_eq_C : B = C := by
      have h14 : U = V := h_U_eq_V
      have h15 : U = B - A := by omega
      have h16 : V = C - A := by omega
      omega
    tauto
  exact ⟨k, y, z, hk_ge_1, hy, hz, h_y_ne_z, h_A, Or.inr ⟨hB_eq2, hC_eq2⟩⟩

theorem existence_of_ramsey_number_for_4_clique (k : ℕ)
  (hk : k ≥ 1):
  ∃ (R : ℕ),
    ∀ (C : Set ℤ)
      (hC_finite : C.Finite)
      (hC_card : C.ncard = k)
      (S : ℕ)
      (hS : S ≥ R)
      (edge_color : ℕ → ℕ → ℤ)
      (h_edge_color_in_C : ∀ (u v : ℕ), u < v → edge_color u v ∈ C),
      ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
        v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
        edge_color v₁ v₂ = c ∧
        edge_color v₁ v₃ = c ∧
        edge_color v₁ v₄ = c ∧
        edge_color v₂ v₃ = c ∧
        edge_color v₂ v₄ = c ∧
        edge_color v₃ v₄ = c := by
  have h1 : ∀ (s t : ℕ)
    (hs : s ≥ 1)
    (ht : t ≥ 1),
    ∃ (R : ℕ), ∀ (S : ℕ)
      (hS : S ≥ R)
      (edge_color : ℕ → ℕ → ℤ)
      (c1 c2 : ℤ)
      (h_c1_ne_c2 : c1 ≠ c2)
      (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)),
    (∃ (f : Fin s → ℕ), (∀ (i : Fin s), f i ≤ S) ∧
        (∀ (i j : Fin s), i < j → f i < f j) ∧
        (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1)) ∨
    (∃ (f : Fin t → ℕ), (∀ (i : Fin t), f i ≤ S) ∧
        (∀ (i j : Fin t), i < j → f i < f j) ∧
        (∀ (i j : Fin t), i < j → edge_color (f i) (f j) = c2)) := by
    intro s t hs ht
    exact ramsey_two_color_general_with_le_S s t hs ht
  have h2 : ∃ (R : ℕ), ∀ (S : ℕ)
    (hS : S ≥ R)
    (edge_color : ℕ → ℕ → ℕ)
    (h_edge_color_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k),
    ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
      (v : Fin 4 → ℕ),
      (∀ (a : Fin 4), v a ≤ S) ∧
      (∀ (a b : Fin 4), a < b → v a < v b) ∧
      (∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = j) := by
    exact natural_k_color_ramsey_from_two_color_with_le_S h1 k hk
  rcases h2 with ⟨R1, h2⟩
  use R1
  intro C hC_finite hC_card S hS edge_color h_edge_color_in_C
  have h3 : ∃ (f : ℤ → ℕ) (g : ℕ → ℤ),
    (∀ (x : ℤ), x ∈ C → 1 ≤ f x ∧ f x ≤ k) ∧
    (∀ (i : ℕ), 1 ≤ i ∧ i ≤ k → g i ∈ C ∧ f (g i) = i) ∧
    (∀ (x : ℤ), x ∈ C → g (f x) = x) := by
    exact color_set_bijection k C hC_finite hC_card hk
  rcases h3 with ⟨f, g, h31, h32, h33⟩
  set edge_color_nat : ℕ → ℕ → ℕ := fun u v => f (edge_color u v) with h_edge_color_nat_def
  have h_edge_color_nat_in_1_to_k : ∀ (u v : ℕ), u < v → 1 ≤ edge_color_nat u v ∧ edge_color_nat u v ≤ k := by
    intro u v huv
    have h4 : edge_color u v ∈ C := h_edge_color_in_C u v huv
    have h5 : 1 ≤ f (edge_color u v) ∧ f (edge_color u v) ≤ k := h31 (edge_color u v) h4
    simpa [h_edge_color_nat_def] using h5
  have h4 : ∃ (j : ℕ) (h_j_bounds : 1 ≤ j ∧ j ≤ k)
    (v : Fin 4 → ℕ),
    (∀ (a : Fin 4), v a ≤ S) ∧
    (∀ (a b : Fin 4), a < b → v a < v b) ∧
    (∀ (a b : Fin 4), a < b → edge_color_nat (v a) (v b) = j) := by
    exact h2 S hS edge_color_nat h_edge_color_nat_in_1_to_k
  rcases h4 with ⟨j, h_j_bounds, v, h_v_le_S, h_v_increasing, h_v_mono_color_j⟩
  set v₁ : ℕ := v 0 with hv1_def
  set v₂ : ℕ := v 1 with hv2_def
  set v₃ : ℕ := v 2 with hv3_def
  set v₄ : ℕ := v 3 with hv4_def
  have h_v1_lt_v2 : v₁ < v₂ := by
    have h : (v 0) < (v 1) := h_v_increasing (0 : Fin 4) (1 : Fin 4) (by decide)
    simpa [hv1_def, hv2_def] using h
  have h_v2_lt_v3 : v₂ < v₃ := by
    have h : (v 1) < (v 2) := h_v_increasing (1 : Fin 4) (2 : Fin 4) (by decide)
    simpa [hv2_def, hv3_def] using h
  have h_v3_lt_v4 : v₃ < v₄ := by
    have h : (v 2) < (v 3) := h_v_increasing (2 : Fin 4) (3 : Fin 4) (by decide)
    simpa [hv3_def, hv4_def] using h
  have h_v4_le_S : v₄ ≤ S := by
    have h : v (3 : Fin 4) ≤ S := h_v_le_S (3 : Fin 4)
    simpa [hv4_def] using h
  set c : ℤ := g j with hc_def
  have hc_in_C : c ∈ C := by
    have h6 : g j ∈ C := (h32 j ⟨h_j_bounds.1, h_j_bounds.2⟩).1
    simpa [hc_def] using h6
  have h_edges_eq_c : ∀ (a b : Fin 4), a < b → edge_color (v a) (v b) = c := by
    intro a b hab
    have h_f_eq_j : f (edge_color (v a) (v b)) = j := by
      have h10 : edge_color_nat (v a) (v b) = j := h_v_mono_color_j a b hab
      simpa [h_edge_color_nat_def] using h10
    have h_in_C : edge_color (v a) (v b) ∈ C := by
      have h11 : v a < v b := h_v_increasing a b hab
      have h12 : edge_color (v a) (v b) ∈ C := h_edge_color_in_C (v a) (v b) h11
      tauto
    have h12 : g (f (edge_color (v a) (v b))) = edge_color (v a) (v b) := h33 (edge_color (v a) (v b)) h_in_C
    have h13 : g j = edge_color (v a) (v b) := by
      rw [h_f_eq_j] at h12
      tauto
    have h14 : edge_color (v a) (v b) = c := by
      have h15 : g j = edge_color (v a) (v b) := h13
      have h16 : c = g j := by
        rw [hc_def]
      linarith
    tauto
  refine' ⟨v₁, v₂, v₃, v₄, c, h_v1_lt_v2, h_v2_lt_v3, h_v3_lt_v4, h_v4_le_S, _⟩
  have h1 : edge_color v₁ v₂ = c := by
    have h11 := h_edges_eq_c (0 : Fin 4) (1 : Fin 4) (by decide)
    simpa [hv1_def, hv2_def] using h11
  have h2 : edge_color v₁ v₃ = c := by
    have h12 := h_edges_eq_c (0 : Fin 4) (2 : Fin 4) (by decide)
    simpa [hv1_def, hv3_def] using h12
  have h3 : edge_color v₁ v₄ = c := by
    have h13 := h_edges_eq_c (0 : Fin 4) (3 : Fin 4) (by decide)
    simpa [hv1_def, hv4_def] using h13
  have h4 : edge_color v₂ v₃ = c := by
    have h14 := h_edges_eq_c (1 : Fin 4) (2 : Fin 4) (by decide)
    simpa [hv2_def, hv3_def] using h14
  have h5 : edge_color v₂ v₄ = c := by
    have h15 := h_edges_eq_c (1 : Fin 4) (3 : Fin 4) (by decide)
    simpa [hv2_def, hv4_def] using h15
  have h6 : edge_color v₃ v₄ = c := by
    have h16 := h_edges_eq_c (2 : Fin 4) (3 : Fin 4) (by decide)
    simpa [hv3_def, hv4_def] using h16
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ramsey_number_for_k_colors_gives_4_tuple_with_6_differences_monochromatic (k : ℕ)
  (hk : k ≥ 1):
  ∃ (R : ℕ),
    ∀ (C : Set ℤ)
      (hC_finite : C.Finite)
      (hC_card : C.ncard = k)
      (S : ℕ)
      (hS : S ≥ R)
      (φ : ℕ → ℤ)
      (hφ : ∀ (n : ℕ), φ n ∈ C),
      ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
        v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
        φ (v₂ - v₁) = c ∧
        φ (v₃ - v₁) = c ∧
        φ (v₄ - v₁) = c ∧
        φ (v₃ - v₂) = c ∧
        φ (v₄ - v₂) = c ∧
        φ (v₄ - v₃) = c := by
  have h1 : ∃ (R : ℕ),
    ∀ (C : Set ℤ)
      (hC_finite : C.Finite)
      (hC_card : C.ncard = k)
      (S : ℕ)
      (hS : S ≥ R)
      (edge_color : ℕ → ℕ → ℤ)
      (h_edge_color_in_C : ∀ (u v : ℕ), u < v → edge_color u v ∈ C),
      ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
        v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
        edge_color v₁ v₂ = c ∧
        edge_color v₁ v₃ = c ∧
        edge_color v₁ v₄ = c ∧
        edge_color v₂ v₃ = c ∧
        edge_color v₂ v₄ = c ∧
        edge_color v₃ v₄ = c := by
    exact existence_of_ramsey_number_for_4_clique k hk
  rcases h1 with ⟨R, hR⟩
  refine' ⟨R, _⟩
  intro C hC_finite hC_card S hS φ hφ
  have h2 : ∃ (edge_color : ℕ → ℕ → ℤ),
    (∀ (u v : ℕ), u < v → v ≤ S → edge_color u v = φ (v - u)) ∧
    (∀ (u v : ℕ), u < v → edge_color u v ∈ C) := by
    exact construct_edge_color_from_phi C hC_finite S φ hφ
  rcases h2 with ⟨edge_color, h_edge_color_eq_phi, h_edge_color_in_C⟩
  have h3 : ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
    v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
    edge_color v₁ v₂ = c ∧
    edge_color v₁ v₃ = c ∧
    edge_color v₁ v₄ = c ∧
    edge_color v₂ v₃ = c ∧
    edge_color v₂ v₄ = c ∧
    edge_color v₃ v₄ = c := by
    exact hR C hC_finite hC_card S hS edge_color h_edge_color_in_C
  rcases h3 with ⟨v₁, v₂, v₃, v₄, c, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  have h4 : φ (v₂ - v₁) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₃) = c := by
    exact monochromatic_clique_gives_6_differences φ v₁ v₂ v₃ v₄ S c h11 h12 h13 h14 edge_color h_edge_color_eq_phi h15 h16 h17 h18 h19 h20
  exact ⟨v₁, v₂, v₃, v₄, c, h11, h12, h13, h14, h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2⟩

theorem ramsey_number_existence_lemma (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_nonempty : C ≠ ∅):
  ∃ (R : ℕ),
    ∀ (S : ℕ)
      (hS : S ≥ R)
      (φ : ℕ → ℤ)
      (hφ : ∀ (n : ℕ), φ n ∈ C),
      ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
        v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
        (∀ (x y : ℕ), x ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → y ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → x < y → φ (y - x) = c) := by
  have h1 : ∃ (k : ℕ), k ≥ 1 ∧ C.ncard = k := by
    exact get_card_ge_one_from_finite_nonempty_set C hC_finite hC_nonempty
  rcases h1 with ⟨k, hk1, hC_ncard⟩
  have h2 : ∃ (R : ℕ),
    ∀ (C' : Set ℤ)
      (hC'_finite : C'.Finite)
      (hC'_card : C'.ncard = k)
      (S : ℕ)
      (hS : S ≥ R)
      (φ : ℕ → ℤ)
      (hφ : ∀ (n : ℕ), φ n ∈ C'),
      ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
        v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
        φ (v₂ - v₁) = c ∧
        φ ( v₃ - v₁) = c ∧
        φ (v₄ - v₁) = c ∧
        φ (v₃ - v₂) = c ∧
        φ (v₄ - v₂) = c ∧
        φ (v₄ - v₃) = c := by
    exact ramsey_number_for_k_colors_gives_4_tuple_with_6_differences_monochromatic k hk1
  rcases h2 with ⟨R, hR⟩
  refine' ⟨R, _⟩
  intro S hS φ hφ
  have h3 : ∃ (v₁ v₂ v₃ v₄ : ℕ) (c : ℤ),
    v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
    φ (v₂ - v₁) = c ∧
    φ (v₃ - v₁) = c ∧
    φ (v₄ - v₁) = c ∧
    φ (v₃ - v₂) = c ∧
    φ (v₄ - v₂) = c ∧
    φ (v₄ - v₃) = c := by
    have h31 := hR C hC_finite hC_ncard S hS φ hφ
    tauto
  rcases h3 with ⟨v₁, v₂, v₃, v₄, c, h11, h12, h13, h14, h_d1, h_d2, h_d3, h_d4, h_d5, h_d6⟩
  have h4 : ∀ (x y : ℕ), x ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → y ∈ ({v₁, v₂, v₃, v₄} : Set ℕ) → x < y → φ (y - x) = c := by
    exact six_differences_monochromatic_entails_all_pairs_monochromatic v₁ v₂ v₃ v₄ c φ h11 h12 h13 h_d1 h_d2 h_d3 h_d4 h_d5 h_d6
  exact ⟨v₁, v₂, v₃, v₄, c, h11, h12, h13, h14, h4⟩

theorem exists_S0_for_monochromatic_clique_4 (C : Set ℤ)
  (hC_finite : C.Finite):
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (v₁ v₂ v₃ v₄ : ℕ),
          v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
          ∃ (c : ℤ),
            φ (v₂ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₃) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₁) = c := by
  by_cases hC : C = ∅
  ·
    have h1 := empty_C_case_lemma C hC_finite hC
    exact h1
  ·
    have h2 := ramsey_number_existence_lemma C hC_finite hC
    rcases h2 with ⟨R, hR⟩
    refine' ⟨R, _⟩
    intro S hS
    intro φ hφ
    rcases hR S hS φ hφ with ⟨v₁, v₂, v₃, v₄, c, h11, h12, h13, h14, h15⟩
    have h16 := clique_to_differences_lemma v₁ v₂ v₃ v₄ φ c h11 h12 h13 h15
    exact ⟨v₁, v₂, v₃, v₄, h11, h12, h13, h14, ⟨c, h16⟩⟩

theorem lemma_ramsey_threshold_existence (C : Set ℤ)
  (hC_finite : C.Finite):
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (u v : ℕ),
          1 ≤ u ∧
          1 ≤ v ∧
          u < v ∧
          u + v ≤ S ∧
          φ u = φ v ∧
          φ v = φ (u + v) := by
  have h1 : ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (v₁ v₂ v₃ v₄ : ℕ),
          v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
          ∃ (c : ℤ),
            φ (v₂ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₃) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₁) = c := by
    exact exists_S0_for_monochromatic_clique_4 C hC_finite
  rcases h1 with ⟨S₀, hS₀⟩
  refine' ⟨S₀, _⟩
  intro S hS_ge_S₀ φ hφ
  have h2 : ∃ (v₁ v₂ v₃ v₄ : ℕ), v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧ ∃ (c : ℤ), φ (v₂ - v₁) = c ∧ φ (v₃ - v₂) = c ∧ φ (v₄ - v₃) = c ∧ φ (v₃ - v₁) = c ∧ φ (v₄ - v₂) = c ∧ φ (v₄ - v₁) = c := by
    exact hS₀ S hS_ge_S₀ φ hφ
  rcases h2 with ⟨v₁, v₂, v₃, v₄, h11, h12, h13, h14, c, h_c1, h_c2, h_c3, h_c4, h_c5, h_c6⟩
  set x₁ := v₂ - v₁ with hx1_def
  set x₂ := v₃ - v₂ with hx2_def
  set x₃ := v₄ - v₃ with hx3_def
  have hx1_ge_1 : x₁ ≥ 1 := by
    omega
  have hx2_ge_1 : x₂ ≥ 1 := by
    omega
  have hx3_ge_1 : x₃ ≥ 1 := by
    omega
  have h3 : φ x₁ = c ∧ φ x₂ = c ∧ φ x₃ = c ∧ φ (x₁ + x₂) = c ∧ φ (x₂ + x₃) = c ∧ φ (x₁ + x₂ + x₃) = c := by
    exact monochromatic_clique_differences_are_uniform φ v₁ v₂ v₃ v₄ h11 h12 h13 c h_c1 h_c2 h_c3 h_c4 h_c5 h_c6
  have h31 : φ x₁ = c := h3.1
  have h32 : φ x₂ = c := h3.2.1
  have h33 : φ x₃ = c := h3.2.2.1
  have h34 : φ (x₁ + x₂) = c := h3.2.2.2.1
  have h35 : φ (x₂ + x₃) = c := h3.2.2.2.2.1
  have h36 : φ (x₁ + x₂ + x₃) = c := h3.2.2.2.2.2
  have h_sum_le_S : x₁ + x₂ + x₃ ≤ S := by
    hint
  have h4 : ∃ (u v : ℕ), 1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
    exact monochromatic_differences_produces_solution φ x₁ x₂ x₃ S hx1_ge_1 hx2_ge_1 hx3_ge_1 c h31 h32 h33 h34 h35 h36 h_sum_le_S
  exact h4

theorem find_special_schur_triple_with_divisibility (χ : ℕ → ℤ)
  (h_finite : (Set.range χ).Finite):
  ∃ (N u v : ℕ),
    N ≥ 1 ∧
    u ≥ 1 ∧
    v ≥ 1 ∧
    u ≠ v ∧
    u < v ∧
    u + v < N ∧
    u ∣ N ∧
    v ∣ N ∧
    (u + v) ∣ N ∧
    χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v)) := by
  set C : Set ℤ := Set.range χ with hC_def
  have hC_finite : C.Finite := h_finite
  have h2 : ∃ (S₀ : ℕ), ∀ (S : ℕ), S ≥ S₀ → ∀ (φ : ℕ → ℤ), (∀ (n : ℕ), φ n ∈ C) → ∃ (u v : ℕ), 1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
    exact lemma_ramsey_threshold_existence C hC_finite
  rcases h2 with ⟨S₀, hS₀⟩
  have h3 : max S₀ 4 ≥ S₀ ∧ max S₀ 4 ≥ 4 := by
    exact lemma_max_preserves_both_inequalities S₀ 4
  rcases h3 with ⟨h31, h32⟩
  set S : ℕ := max S₀ 4 with hS_def
  have hS_ge_S₀ : S ≥ S₀ := h31
  have hS_ge_4 : S ≥ 4 := h32
  have h4 : ∀ (k : ℕ), (1 ≤ k ∧ k ≤ S) → (k ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := by
    exact lemma_factorial_divides_and_lower_bound S hS_ge_4
  set N : ℕ := Nat.factorial S with hN_def
  have h_S_lt_N : S < N := by
    have h41 := (h4 1 ⟨by norm_num, by linarith⟩)
    exact h41.2
  set φ : ℕ → ℤ := fun (k : ℕ) => χ (N / k) with hφ_def
  have h5 : ∀ (n : ℕ), φ n ∈ C := by
    exact lemma_aux_coloring_range_subset_original_range χ S C (by rw [hC_def])
  have h6 : ∃ (u v : ℕ), 1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
    exact hS₀ S hS_ge_S₀ φ h5
  rcases h6 with ⟨u, v, h_u_ge_1, h_v_ge_1, h_u_lt_v, h_sum_le_S, h1_eq, h2_eq⟩
  have h_u_ne_v : u ≠ v := by
    linarith
  have h_v_le_S : v ≤ S := by
    exact lemma_v_le_S_from_sum_le_S_and_u_lt_v u v S h_u_ge_1 h_v_ge_1 h_u_lt_v h_sum_le_S
  have h_u_le_S : u ≤ S := by
    exact lemma_u_le_S_from_u_lt_v_and_v_le_S u v S h_u_lt_v h_v_le_S
  have h_sum_ge_1 : 1 ≤ u + v := by
    exact lemma_sum_of_two_naturals_ge_one u v h_u_ge_1 h_v_ge_1
  have h_u_div_N : u ∣ N := by
    have h4_u : (u ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := h4 u ⟨h_u_ge_1, h_u_le_S⟩
    exact h4_u.1
  have h_v_div_N : v ∣ N := by
    have h4_v : (v ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := h4 v ⟨h_v_ge_1, h_v_le_S⟩
    exact h4_v.1
  have h_sum_div_N : (u + v) ∣ N := by
    have h4_sum : ((u + v) ∣ Nat.factorial S) ∧ (S < Nat.factorial S) := h4 (u + v) ⟨h_sum_ge_1, h_sum_le_S⟩
    exact h4_sum.1
  have h_sum_lt_N : u + v < N := by
    exact lemma_inequality_transitivity_sum_lt_N u v S N h_sum_le_S h_S_lt_N
  have h_N_ge_1 : N ≥ 1 := by
    have hS_ge_1 : S ≥ 1 := by linarith
    have h91 : Nat.factorial S ≥ 1 := lemma_factorial_is_at_least_one_when_S_ge_one S hS_ge_1
    linarith [hN_def]
  have h_chi1 : χ (N / u) = χ (N / v) := by
    simpa [hφ_def] using h1_eq
  have h_chi2 : χ (N / v) = χ (N / (u + v)) := by
    simpa [hφ_def] using h2_eq
  exact ⟨N, u, v, h_N_ge_1, h_u_ge_1, h_v_ge_1, h_u_ne_v, h_u_lt_v, h_sum_lt_N, h_u_div_N, h_v_div_N, h_sum_div_N, h_chi1, h_chi2⟩

theorem find_monochromatic_parametric_variables_in_naturals (χ : ℕ → ℤ)
  (h_finite : (Set.range χ).Finite):
  ∃ (k y z : ℕ),
    k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧
    χ (k * y * z) = χ (k * z * (y + z)) ∧
    χ (k * z * (y + z)) = χ (k * y * (y + z)) := by
  have h1 : ∃ (N u v : ℕ), N ≥ 1 ∧ u ≥ 1 ∧ v ≥ 1 ∧ u ≠ v ∧ u < v ∧ u + v < N ∧ u ∣ N ∧ v ∣ N ∧ (u + v) ∣ N ∧ χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v)) := by
    exact find_special_schur_triple_with_divisibility χ h_finite
  rcases h1 with ⟨N, u, v, hN, hu, hv, h_ne, h_lt1, h_lt2, hu_dvd_N, hv_dvd_N, hsum_dvd_N, h_color1, h_color2⟩
  have h_color : χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v)) := ⟨h_color1, h_color2⟩
  have h2 : ∃ (A B C : ℕ), A ≥ 1 ∧ B ≥ 1 ∧ C ≥ 1 ∧ B ≠ C ∧ A * (B + C) = B * C ∧ χ A = χ B ∧ χ B = χ C := by
    exact schur_triple_produces_unit_fraction_solution χ N u v hN hu hv h_ne h_lt1 h_lt2 hu_dvd_N hv_dvd_N hsum_dvd_N h_color
  rcases h2 with ⟨A, B, C, hA, hB, hC, h_ne', h_eq, h_color3, h_color4⟩
  have h_color5 : χ A = χ B ∧ χ B = χ C := ⟨h_color3, h_color4⟩
  have h3 : ∃ (k y z : ℕ), k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧ A = k * y * z ∧ ((B = k * z * (y + z) ∧ C = k * y * (y + z)) ∨ (B = k * y * (y + z) ∧ C = k * z * (y + z))) := by
    exact unit_fraction_solution_has_parametric_form A B C hA hB hC h_ne' h_eq
  rcases h3 with ⟨k, y, z, hk, hy, hz, h_y_ne_z, hA_eq, h4⟩
  cases h4 with
  | inl h41 =>
    have h411 : B = k * z * (y + z) := h41.1
    have h412 : C = k * y * (y + z) := h41.2
    have h51 : χ A = χ B := h_color5.1
    have h52 : χ B = χ C := h_color5.2
    have h61 : χ (k * y * z) = χ (k * z * (y + z)) := by
      have h611 : χ A = χ B := h51
      rw [hA_eq, h411] at h611
      exact h611
    have h62 : χ (k * z * (y + z)) = χ (k * y * (y + z)) := by
      have h621 : χ B = χ C := h52
      rw [h411, h412] at h621
      exact h621
    exact ⟨k, y, z, hk, hy, hz, h_y_ne_z, h61, h62⟩
  | inr h42 =>
    have h421 : B = k * y * (y + z) := h42.1
    have h422 : C = k * z * (y + z) := h42.2
    have h51 : χ A = χ B := h_color5.1
    have h52 : χ B = χ C := h_color5.2
    have h71 : χ (k * y * z) = χ (k * y * (y + z)) := by
      have h711 : χ A = χ B := h51
      rw [hA_eq, h421] at h711
      exact h711
    have h72 : χ (k * y * (y + z)) = χ (k * z * (y + z)) := by
      have h721 : χ B = χ C := h52
      rw [h421, h422] at h721
      exact h721
    have h73 : χ (k * y * z) = χ (k * z * (y + z)) := by
      calc
        χ (k * y * z) = χ (k * y * (y + z)) := h71
        _ = χ (k * z * (y + z)) := h72
    have h74 : χ (k * z * (y + z)) = χ (k * y * (y + z)) := by
      have h741 : χ (k * y * (y + z)) = χ (k * z * (y + z)) := h72
      exact h741.symm
    exact ⟨k, y, z, hk, hy, hz, h_y_ne_z, h73, h74⟩

theorem erdos_303 :
  (∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
    ∃ (a b c : ℤ),
    [a, b, c, 0].Nodup ∧
    (1/a : ℝ) = 1/b + 1/c ∧
    (𝓒 '' {a, b, c}).Subsingleton) := by
  intro 𝓒 h_finite
  have h1 : ∃ (χ : ℕ → ℤ), (Set.range χ).Finite ∧ (∀ (n : ℕ), χ n = 𝓒 (n : ℤ)) :=
    get_finite_natural_coloring_from_integer_coloring 𝓒 h_finite
  rcases h1 with ⟨χ, h_χ_finite, h_χ_def⟩
  have h2 : ∃ (k y z : ℕ), k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧ χ (k * y * z) = χ (k * z * (y + z)) ∧ χ (k * z * (y + z)) = χ (k * y * (y + z)) :=
    find_monochromatic_parametric_variables_in_naturals χ h_χ_finite
  rcases h2 with ⟨k, y, z, hk, hy, hz, hne, h_monochromatic1, h_monochromatic2⟩
  have h3 : (k * y * z : ℤ) ≠ 0 ∧
            (k * z * (y + z) : ℤ) ≠ 0 ∧
            (k * y * (y + z) : ℤ) ≠ 0 ∧
            (k * y * z : ℤ) ≠ (k * z * (y + z) : ℤ) ∧
            (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) ∧
            (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) ∧
            (1 / ((k * y * z : ℤ) : ℝ)) = (1 / ((k * z * (y + z) : ℤ) : ℝ)) + (1 / ((k * y * (y + z) : ℤ) : ℝ)) :=
    verify_parametric_solution_is_distinct_and_satisfies_equation k y z hk hy hz hne
  have ha_ne_zero : (k * y * z : ℤ) ≠ 0 := h3.1
  have hb_ne_zero : (k * z * (y + z) : ℤ) ≠ 0 := h3.2.1
  have hc_ne_zero : (k * y * (y + z) : ℤ) ≠ 0 := h3.2.2.1
  have ha_ne_b : (k * y * z : ℤ) ≠ (k * z * (y + z) : ℤ) := h3.2.2.2.1
  have hb_ne_c : (k * z * (y + z) : ℤ) ≠ (k * y * (y + z) : ℤ) := h3.2.2.2.2.1
  have ha_ne_c : (k * y * z : ℤ) ≠ (k * y * (y + z) : ℤ) := h3.2.2.2.2.2.1
  have h_equation : (1 / ((k * y * z : ℤ) : ℝ)) = (1 / ((k * z * (y + z) : ℤ) : ℝ)) + (1 / ((k * y * (y + z) : ℤ) : ℝ)) := h3.2.2.2.2.2.2
  have h4 : (𝓒 '' {((k * y * z : ℕ) : ℤ), ((k * z * (y + z) : ℕ) : ℤ), ((k * y * (y + z) : ℕ) : ℤ)}).Subsingleton :=
    transfer_monochromatic_property_from_natural_to_integer 𝓒 χ h_χ_def k y z hk hy hz ⟨h_monochromatic1, h_monochromatic2⟩
  have h5 : [(k * y * z : ℤ), (k * z * (y + z) : ℤ), (k * y * (y + z) : ℤ), 0].Nodup :=
    distinct_nonzero_integers_form_nodup_list_with_zero ((k * y * z : ℤ)) ((k * z * (y + z) : ℤ)) ((k * y * (y + z) : ℤ)) ha_ne_zero hb_ne_zero hc_ne_zero ha_ne_b hb_ne_c ha_ne_c
  refine' ⟨(k * y * z : ℤ), (k * z * (y + z) : ℤ), (k * y * (y + z) : ℤ), _⟩
  constructor
  · simpa using h5
  · constructor
    · simpa using h_equation
    · simpa [Set.ext_iff] using h4

#print axioms erdos_303
-- 'Erdos303.erdos_303' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos303
