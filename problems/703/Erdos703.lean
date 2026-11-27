import Mathlib

namespace Erdos703

/-
# Erdős Problem 703

Let $r\geq 1$ and define $T(n,r)$ to be maximal such that there exists a family $\mathcal{F}$ of
subsets of $\{1,\ldots,n\}$ of size $T(n,r)$ such that $\lvert A\cap B\rvert\neq r$ for all
$A,B\in \mathcal{F}$. Estimate $T(n,r)$ for $r\geq 2$. In particular, is it true that for every
$\epsilon>0$ there exists $\delta>0$ such that for all $\epsilon n<r<(1/2-\epsilon) n$ we have
$$T(n,r)<(2-\delta)^n?$$

The answer to the second question is **yes**, proved by Frankl and Rödl [FrRo87]
(`erdos_703_gap`). For the first, Frankl and Füredi [FrFu84b] determined $T(n,r)$ exactly for
fixed $r$ and $n$ sufficiently large in terms of $r$: it is attained by the family of all sets
of size $< r$ or $> (n+r)/2$, together with, when $n + r$ is even, the sets of size $(n+r)/2$
avoiding a fixed element (`erdos_703_exact`, with `ffBound n r` the size of that family and
$T(n,0) = 2^{n-1}$). `erdos_703` states both results.

Formalised by Collin Yuanjie Ren in `CollinYuanjieRen/awards` (submission JSP-000573), building on
the `plby/lean-proofs` formalisation (`ErdosProblems/Erdos703.lean` and its four supporting
modules), which supplies the definition of $T$, the Frankl--Füredi lower-bound constructions and
the Frankl--Rödl gap. The twelve modules forming the closure are flattened here in dependency
order. plby's final theorem is renamed `erdos_703_gap` and its `#print axioms` line is removed.
`erdos_703` is added here: it combines `erdos_703_gap` and `erdos_703_exact`, and adds no
mathematical content.

Declarations that `erdos_703` does not depend on have been removed.
-/

/-! ### Upstream module `JSP573/External/Erdos703/Iteration.lean` -/

namespace Erdos703Iteration

/-!
An axiom-free formalization of the finite coordinate-section part of the
Frankl--Rödl forbidden-intersection iteration.  The two isoperimetric endpoint
estimates are deliberately abstracted as hypotheses at the end of the file.
-/

abbrev Family (m : ℕ) := Finset (Finset (Fin m))

def liftZero {m : ℕ} (A : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  A.map Fin.castSuccEmb

def liftOne {m : ℕ} (A : Finset (Fin m)) : Finset (Fin (m + 1)) :=
  insert (Fin.last m) (liftZero A)

def sectionZero {m : ℕ} (F : Family (m + 1)) : Family m :=
  Finset.univ.filter fun A ↦ liftZero A ∈ F

def sectionOne {m : ℕ} (F : Family (m + 1)) : Family m :=
  Finset.univ.filter fun A ↦ liftOne A ∈ F

def dropLast {m : ℕ} (S : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i ↦ i.castSucc ∈ S

@[simp] lemma mem_sectionZero {m : ℕ} {F : Family (m + 1)} {A : Finset (Fin m)} :
    A ∈ sectionZero F ↔ liftZero A ∈ F := by
  simp [sectionZero]

@[simp] lemma mem_sectionOne {m : ℕ} {F : Family (m + 1)} {A : Finset (Fin m)} :
    A ∈ sectionOne F ↔ liftOne A ∈ F := by
  simp [sectionOne]

@[simp] lemma last_not_mem_liftZero {m : ℕ} (A : Finset (Fin m)) :
    Fin.last m ∉ liftZero A := by
  simp [liftZero]

@[simp] lemma dropLast_liftZero {m : ℕ} (A : Finset (Fin m)) :
    dropLast (liftZero A) = A := by
  ext i
  simp [dropLast, liftZero]

@[simp] lemma dropLast_liftOne {m : ℕ} (A : Finset (Fin m)) :
    dropLast (liftOne A) = A := by
  ext i
  simp [dropLast, liftOne, liftZero]

lemma liftZero_dropLast_of_last_not_mem {m : ℕ} {S : Finset (Fin (m + 1))}
    (hS : Fin.last m ∉ S) : liftZero (dropLast S) = S := by
  ext x
  by_cases hx : x = Fin.last m
  · subst x
    simp [hS]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hx
    simp [dropLast, liftZero]

lemma liftOne_dropLast_of_last_mem {m : ℕ} {S : Finset (Fin (m + 1))}
    (hS : Fin.last m ∈ S) : liftOne (dropLast S) = S := by
  ext x
  by_cases hx : x = Fin.last m
  · subst x
    simp [liftOne, hS]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hx
    simp [dropLast, liftOne, liftZero]

@[simp] lemma liftZero_inter {m : ℕ} (A B : Finset (Fin m)) :
    liftZero (A ∩ B) = liftZero A ∩ liftZero B := by
  exact Finset.map_inter A B

@[simp] lemma liftZero_inter_liftOne {m : ℕ} (A B : Finset (Fin m)) :
    liftZero A ∩ liftOne B = liftZero (A ∩ B) := by
  calc
    liftZero A ∩ liftOne B = liftZero A ∩ liftZero B := by
      ext x
      by_cases hx : x = Fin.last m <;> simp [liftOne, hx]
    _ = liftZero (A ∩ B) := (liftZero_inter A B).symm

@[simp] lemma liftOne_inter_liftZero {m : ℕ} (A B : Finset (Fin m)) :
    liftOne A ∩ liftZero B = liftZero (A ∩ B) := by
  rw [Finset.inter_comm]
  simpa [Finset.inter_comm] using liftZero_inter_liftOne B A

@[simp] lemma liftOne_inter {m : ℕ} (A B : Finset (Fin m)) :
    liftOne A ∩ liftOne B = liftOne (A ∩ B) := by
  ext x
  by_cases hx : x = Fin.last m
  · simp [liftOne, hx]
  · simp only [liftOne, Finset.mem_inter, Finset.mem_insert, hx, false_or]
    constructor
    · rintro ⟨hA, hB⟩
      have hxmem : x ∈ liftZero A ∩ liftZero B := Finset.mem_inter.mpr ⟨hA, hB⟩
      rw [← liftZero_inter] at hxmem
      exact hxmem
    · intro hxmem
      have : x ∈ liftZero A ∩ liftZero B := by
        rw [← liftZero_inter]
        exact hxmem
      exact Finset.mem_inter.mp this

@[simp] lemma card_liftZero {m : ℕ} (A : Finset (Fin m)) :
    (liftZero A).card = A.card := by
  simp [liftZero]

@[simp] lemma card_liftOne {m : ℕ} (A : Finset (Fin m)) :
    (liftOne A).card = A.card + 1 := by
  simp [liftOne]

@[simp] lemma card_liftZero_inter {m : ℕ} (A B : Finset (Fin m)) :
    (liftZero A ∩ liftZero B).card = (A ∩ B).card := by
  rw [← liftZero_inter, card_liftZero]

@[simp] lemma card_liftOne_inter_liftZero {m : ℕ} (A B : Finset (Fin m)) :
    (liftOne A ∩ liftZero B).card = (A ∩ B).card := by
  rw [liftOne_inter_liftZero, card_liftZero]

@[simp] lemma card_liftOne_inter {m : ℕ} (A B : Finset (Fin m)) :
    (liftOne A ∩ liftOne B).card = (A ∩ B).card + 1 := by
  simp

def CrossAvoids {m : ℕ} (a b : ℕ) (F G : Family m) : Prop :=
  ∀ A ∈ F, ∀ B ∈ G, (A ∩ B).card < a ∨ b < (A ∩ B).card

lemma sectionOne_sectionOne_avoids {m a b : ℕ} {F G : Family (m + 1)}
    (h : CrossAvoids (a + 1) (b + 1) F G) :
    CrossAvoids a b (sectionOne F) (sectionOne G) := by
  intro A hA B hB
  have h' := h (liftOne A) (by simpa using hA) (liftOne B) (by simpa using hB)
  simp only [card_liftOne_inter] at h'
  omega

lemma sectionZero_union_avoids {m a b : ℕ} {F G : Family (m + 1)}
    (h : CrossAvoids a b F G) :
    CrossAvoids a b (sectionZero F) (sectionZero G ∪ sectionOne G) := by
  intro A hA B hB
  rw [Finset.mem_union] at hB
  rcases hB with hB | hB
  · simpa using h (liftZero A) (by simpa using hA) (liftZero B) (by simpa using hB)
  · simpa using h (liftZero A) (by simpa using hA) (liftOne B) (by simpa using hB)

lemma sectionOne_inter_avoids {m a b : ℕ} (hab : a + 1 ≤ b)
    {F G : Family (m + 1)} (h : CrossAvoids (a + 1) b F G) :
    CrossAvoids a b (sectionOne F) (sectionZero G ∩ sectionOne G) := by
  intro A hA B hB
  have hB0 : B ∈ sectionZero G := (Finset.mem_inter.mp hB).1
  have hB1 : B ∈ sectionOne G := (Finset.mem_inter.mp hB).2
  have hz := h (liftOne A) (by simpa using hA) (liftZero B) (by simpa using hB0)
  have ho := h (liftOne A) (by simpa using hA) (liftOne B) (by simpa using hB1)
  simp only [card_liftOne_inter_liftZero] at hz
  simp only [card_liftOne_inter] at ho
  by_cases hs : (A ∩ B).card < a
  · exact Or.inl hs
  right
  by_contra hnb
  have hsle : (A ∩ B).card ≤ b := Nat.le_of_not_gt hnb
  have hale : a ≤ (A ∩ B).card := Nat.le_of_not_gt hs
  by_cases heq : (A ∩ B).card = a
  · subst heq
    omega
  · have ha1 : a + 1 ≤ (A ∩ B).card := by omega
    omega

noncomputable def density {m : ℕ} (F : Family m) : ℝ :=
  F.card / (2 : ℝ) ^ m

lemma card_sectionZero {m : ℕ} (F : Family (m + 1)) :
    (sectionZero F).card = (F.filter fun S ↦ Fin.last m ∉ S).card := by
  classical
  apply Finset.card_bij' (fun A _ ↦ liftZero A) (fun S _ ↦ dropLast S)
  · intro A hA
    simp only [Finset.mem_filter]
    exact ⟨(by simpa using hA), last_not_mem_liftZero A⟩
  · intro S hS
    simp only [Finset.mem_filter] at hS
    rw [mem_sectionZero, liftZero_dropLast_of_last_not_mem hS.2]
    exact hS.1
  · intro A hA
    exact dropLast_liftZero A
  · intro S hS
    exact liftZero_dropLast_of_last_not_mem (Finset.mem_filter.mp hS).2

lemma card_sectionOne {m : ℕ} (F : Family (m + 1)) :
    (sectionOne F).card = (F.filter fun S ↦ Fin.last m ∈ S).card := by
  classical
  apply Finset.card_bij' (fun A _ ↦ liftOne A) (fun S _ ↦ dropLast S)
  · intro A hA
    simp only [Finset.mem_filter]
    exact ⟨(by simpa using hA), by simp [liftOne]⟩
  · intro S hS
    simp only [Finset.mem_filter] at hS
    rw [mem_sectionOne, liftOne_dropLast_of_last_mem hS.2]
    exact hS.1
  · intro A hA
    exact dropLast_liftOne A
  · intro S hS
    exact liftOne_dropLast_of_last_mem (Finset.mem_filter.mp hS).2

lemma card_sections_add {m : ℕ} (F : Family (m + 1)) :
    (sectionZero F).card + (sectionOne F).card = F.card := by
  classical
  rw [card_sectionZero, card_sectionOne]
  let F0 := F.filter fun S ↦ Fin.last m ∉ S
  let F1 := F.filter fun S ↦ Fin.last m ∈ S
  have hu : F0 ∪ F1 = F := by
    ext S
    by_cases hSF : S ∈ F <;> by_cases hSl : Fin.last m ∈ S <;> simp [F0, F1, hSF, hSl]
  have hi : F0 ∩ F1 = ∅ := by
    ext S
    by_cases hSF : S ∈ F <;> by_cases hSl : Fin.last m ∈ S <;> simp [F0, F1, hSF, hSl]
  have hcard := Finset.card_union_add_card_inter F0 F1
  rw [hu, hi] at hcard
  simpa using hcard.symm

lemma density_sections_add {m : ℕ} (F : Family (m + 1)) :
    density (sectionZero F) + density (sectionOne F) = 2 * density F := by
  rw [density, density, density]
  have hcast : ((sectionZero F).card : ℝ) + (sectionOne F).card = F.card := by
    exact_mod_cast card_sections_add F
  rw [← add_div, hcast, pow_succ]
  ring

lemma density_union_add_inter {m : ℕ} (F G : Family m) :
    density (F ∪ G) + density (F ∩ G) = density F + density G := by
  rw [density, density, density, density, ← add_div, ← add_div]
  congr 1
  exact_mod_cast Finset.card_union_add_card_inter F G

lemma density_inter_le_left {m : ℕ} (F G : Family m) : density (F ∩ G) ≤ density F := by
  rw [density, density]
  gcongr
  exact show F ∩ G ⊆ F from Finset.inter_subset_left

lemma density_union_ge_left {m : ℕ} (F G : Family m) : density F ≤ density (F ∪ G) := by
  rw [density, density]
  gcongr
  exact show F ⊆ F ∪ G by intro x hx; simp [hx]

lemma fr_density_algebra_aux {s x y : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (hy : 0 ≤ y)
    (hsmall : (1 + y) ^ 2 ≤ 1 + s)
    (hfail : (1 + x) * (1 - y) ≤ 1 + s) :
    1 - s - 2 * s ^ 2 ≤ (1 + y) * (1 - x) := by
  have hy2 : 2 * y ≤ s := by
    nlinarith [sq_nonneg y]
  have hy_le : y ≤ 1 / 20 := by nlinarith
  have hone_y : 0 < 1 - y := by nlinarith
  have hxy : x * y ≤ s ^ 2 := by
    have hx_le : x ≤ 2 * s := by
      by_contra hnot
      have hgt : 2 * s < x := lt_of_not_ge hnot
      have hmul : 2 * s * (1 - y) < x * (1 - y) :=
        mul_lt_mul_of_pos_right hgt hone_y
      have hupper : x * (1 - y) ≤ s + y := by nlinarith
      have hlower : s + y ≤ 2 * s * (1 - y) := by
        nlinarith [mul_nonneg hs0 hy]
      linarith
    calc
      x * y ≤ (2 * s) * y := by gcongr
      _ = s * (2 * y) := by ring
      _ ≤ s * s := by gcongr
      _ = s ^ 2 := by ring
  nlinarith

lemma fr_bad_product_of_small_left
    {s f f0 f1 g gu gi : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10)
    (hf : 0 < f) (hg : 0 < g)
    (hfsum : f0 + f1 = 2 * f) (hgsum : gu + gi = 2 * g) (horder : gi ≤ gu)
    (hsmall : f1 ^ 2 ≤ (1 + s) * f ^ 2)
    (hfail : f0 * gu ≤ (1 + s) * f * g) :
    (1 - s - 2 * s ^ 2) * f * g ≤ f1 * gi := by
  let x := gu / g - 1
  let y := f1 / f - 1
  have hfg : 0 < f * g := mul_pos hf hg
  have hf2 : 0 < f ^ 2 := sq_pos_of_pos hf
  have hgu_eq : gu = (1 + x) * g := by
    dsimp [x]
    field_simp
    ring
  have hgi_eq : gi = (1 - x) * g := by
    calc
      gi = 2 * g - gu := by linarith [hgsum]
      _ = (1 - x) * g := by rw [hgu_eq]; ring
  have hf1_eq : f1 = (1 + y) * f := by
    dsimp [y]
    field_simp
    ring
  have hf0_eq : f0 = (1 - y) * f := by
    calc
      f0 = 2 * f - f1 := by linarith [hfsum]
      _ = (1 - y) * f := by rw [hf1_eq]; ring
  have hx : 0 ≤ x := by
    rw [hgu_eq, hgi_eq] at horder
    nlinarith
  by_cases hycase : 0 ≤ y
  · have hsmall' : (1 + y) ^ 2 ≤ 1 + s := by
      rw [hf1_eq, mul_pow] at hsmall
      nlinarith
    have hfail' : (1 + x) * (1 - y) ≤ 1 + s := by
      rw [hf0_eq, hgu_eq] at hfail
      have hscaled : ((1 + x) * (1 - y)) * (f * g) ≤ (1 + s) * (f * g) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hfail
      exact le_of_mul_le_mul_right hscaled hfg
    have haux := fr_density_algebra_aux hs0 hs hycase hsmall' hfail'
    rw [hf1_eq, hgi_eq]
    have hscaled := mul_le_mul_of_nonneg_right haux (le_of_lt hfg)
    nlinarith
  · have hy : y < 0 := lt_of_not_ge hycase
    have hfail' : ((1 - y) * (1 + x)) * (f * g) ≤ (1 + s) * (f * g) := by
      rw [hf0_eq, hgu_eq] at hfail
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfail
    have hfail'' : (1 - y) * (1 + x) ≤ 1 + s :=
      le_of_mul_le_mul_right hfail' hfg
    have hxy : x * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hy)
    have hraw : 1 - s - 2 * s ^ 2 ≤ (1 + y) * (1 - x) := by
      nlinarith [sq_nonneg s]
    rw [hf1_eq, hgi_eq]
    have hscaled := mul_le_mul_of_nonneg_right hraw (le_of_lt hfg)
    nlinarith

lemma small_square_or_of_product
    {c f f1 g g1 : ℝ} (hc : 0 < c) (hf : 0 < f) (hg : 0 < g)
    (hf1 : 0 ≤ f1) (hg1 : 0 ≤ g1)
    (hprod : f1 * g1 ≤ c * f * g) :
    f1 ^ 2 ≤ c * f ^ 2 ∨ g1 ^ 2 ≤ c * g ^ 2 := by
  by_contra h
  push Not at h
  have hf1pos : 0 < f1 := by nlinarith [sq_nonneg f1]
  have hg1pos : 0 < g1 := by nlinarith [sq_nonneg g1]
  have hleft := mul_lt_mul_of_pos_right h.1 (sq_pos_of_pos hg1pos)
  have hright := mul_lt_mul_of_pos_left h.2 (mul_pos hc (sq_pos_of_pos hf))
  have hstrict : (c * f * g) ^ 2 < (f1 * g1) ^ 2 := by
    calc
      (c * f * g) ^ 2 = (c * f ^ 2) * (c * g ^ 2) := by ring
      _ < (c * f ^ 2) * g1 ^ 2 := hright
      _ < f1 ^ 2 * g1 ^ 2 := hleft
      _ = (f1 * g1) ^ 2 := by ring
  have hnonneg : 0 ≤ c * f * g := by positivity
  have hsquare : (f1 * g1) ^ 2 ≤ (c * f * g) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hf1 hg1) hnonneg).2 hprod
  exact (not_lt_of_ge hsquare hstrict)

lemma density_nonneg {m : ℕ} (F : Family m) : 0 ≤ density F := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

lemma density_le_one {m : ℕ} (F : Family m) : density F ≤ 1 := by
  rw [density, div_le_one (by positivity : (0 : ℝ) < 2 ^ m)]
  have h := F.card_le_univ
  exact_mod_cast (by simpa using h)

lemma crossAvoids_comm {m a b : ℕ} {F G : Family m} (h : CrossAvoids a b F G) :
    CrossAvoids a b G F := by
  intro B hB A hA
  simpa [Finset.inter_comm] using h A hA B hB

/-- One coordinate step of the Frankl--Rödl iteration.  A good step either
keeps or shifts the forbidden interval and gains a factor `1+s`; a bad step
widens the interval and loses only the factor `1-s-2*s^2`. -/
lemma fr_one_step {m a b : ℕ} {F G : Family (m + 1)} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (ha : 0 < a) (hab : a ≤ b)
    (havoid : CrossAvoids a b F G) :
    (∃ F' G' : Family m,
        CrossAvoids (a - 1) (b - 1) F' G' ∧
          (1 + s) * density F * density G ≤ density F' * density G') ∨
    (∃ F' G' : Family m,
        CrossAvoids a b F' G' ∧
          (1 + s) * density F * density G ≤ density F' * density G') ∨
    (∃ F' G' : Family m,
        CrossAvoids (a - 1) b F' G' ∧
          (1 - s - 2 * s ^ 2) * density F * density G ≤
            density F' * density G') := by
  have haeq : a - 1 + 1 = a := by omega
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  have hbeq : b - 1 + 1 = b := by omega
  have hshiftAvoid :
      CrossAvoids (a - 1) (b - 1) (sectionOne F) (sectionOne G) := by
    rw [← haeq, ← hbeq] at havoid
    exact sectionOne_sectionOne_avoids havoid
  have hsameAvoid :
      CrossAvoids a b (sectionZero F) (sectionZero G ∪ sectionOne G) :=
    sectionZero_union_avoids havoid
  by_cases hfzero : density F = 0
  · right; left
    refine ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, ?_⟩
    have hnonneg := mul_nonneg (density_nonneg (sectionZero F))
      (density_nonneg (sectionZero G ∪ sectionOne G))
    simpa [hfzero] using hnonneg
  by_cases hgzero : density G = 0
  · right; left
    refine ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, ?_⟩
    have hnonneg := mul_nonneg (density_nonneg (sectionZero F))
      (density_nonneg (sectionZero G ∪ sectionOne G))
    simpa [hgzero] using hnonneg
  have hfpos : 0 < density F := lt_of_le_of_ne (density_nonneg F) (Ne.symm hfzero)
  have hgpos : 0 < density G := lt_of_le_of_ne (density_nonneg G) (Ne.symm hgzero)
  let f0 := density (sectionZero F)
  let f1 := density (sectionOne F)
  let g0 := density (sectionZero G)
  let g1 := density (sectionOne G)
  by_cases hshift : (1 + s) * density F * density G ≤ f1 * g1
  · left
    exact ⟨sectionOne F, sectionOne G, hshiftAvoid, hshift⟩
  have hshiftFail : f1 * g1 ≤ (1 + s) * density F * density G :=
    le_of_lt (lt_of_not_ge hshift)
  have hcpos : 0 < 1 + s := by linarith
  have hsmall := small_square_or_of_product hcpos hfpos hgpos
    (density_nonneg (sectionOne F)) (density_nonneg (sectionOne G)) hshiftFail
  rcases hsmall with hsmallF | hsmallG
  · let gu := density (sectionZero G ∪ sectionOne G)
    let gi := density (sectionZero G ∩ sectionOne G)
    have hfsum : f0 + f1 = 2 * density F := density_sections_add F
    have hgsum : gu + gi = 2 * density G := by
      calc
        gu + gi = g0 + g1 := density_union_add_inter _ _
        _ = 2 * density G := density_sections_add G
    have horder : gi ≤ gu :=
      (density_inter_le_left (sectionZero G) (sectionOne G)).trans
        (density_union_ge_left (sectionZero G) (sectionOne G))
    by_cases hgood : (1 + s) * density F * density G ≤ f0 * gu
    · right; left
      exact ⟨sectionZero F, sectionZero G ∪ sectionOne G, hsameAvoid, hgood⟩
    · right; right
      have hwidenAvoid :
          CrossAvoids (a - 1) b (sectionOne F)
            (sectionZero G ∩ sectionOne G) := by
        have hab' : a - 1 + 1 ≤ b := by omega
        rw [← haeq] at havoid
        exact sectionOne_inter_avoids hab' havoid
      have hbad := fr_bad_product_of_small_left hs0 hs hfpos hgpos
        hfsum hgsum horder hsmallF (le_of_lt (lt_of_not_ge hgood))
      exact ⟨sectionOne F, sectionZero G ∩ sectionOne G, hwidenAvoid, hbad⟩
  · let fu := density (sectionZero F ∪ sectionOne F)
    let fi := density (sectionZero F ∩ sectionOne F)
    have hgsum : g0 + g1 = 2 * density G := density_sections_add G
    have hfsum : fu + fi = 2 * density F := by
      calc
        fu + fi = f0 + f1 := density_union_add_inter _ _
        _ = 2 * density F := density_sections_add F
    have horder : fi ≤ fu :=
      (density_inter_le_left (sectionZero F) (sectionOne F)).trans
        (density_union_ge_left (sectionZero F) (sectionOne F))
    by_cases hgood : (1 + s) * density G * density F ≤ g0 * fu
    · right; left
      have hsymm := sectionZero_union_avoids (crossAvoids_comm havoid)
      refine ⟨sectionZero G, sectionZero F ∪ sectionOne F, hsymm, ?_⟩
      nlinarith
    · right; right
      have hwidenAvoid :
          CrossAvoids (a - 1) b (sectionOne G)
            (sectionZero F ∩ sectionOne F) := by
        have hab' : a - 1 + 1 ≤ b := by omega
        have hsymmetric := crossAvoids_comm havoid
        rw [← haeq] at hsymmetric
        exact sectionOne_inter_avoids hab' hsymmetric
      have hbad := fr_bad_product_of_small_left hs0 hs hgpos hfpos
        hgsum hfsum horder hsmallG (le_of_lt (lt_of_not_ge hgood))
      refine ⟨sectionOne G, sectionZero F ∩ sectionOne F, hwidenAvoid, ?_⟩
      nlinarith

inductive FRStep (s : ℝ) {m a b : ℕ} (F G : Family (m + 1)) : Type
  | shifted (F' G' : Family m)
      (avoids : CrossAvoids (a - 1) (b - 1) F' G')
      (gain : (1 + s) * density F * density G ≤ density F' * density G')
  | same (F' G' : Family m)
      (avoids : CrossAvoids a b F' G')
      (gain : (1 + s) * density F * density G ≤ density F' * density G')
  | widened (F' G' : Family m)
      (avoids : CrossAvoids (a - 1) b F' G')
      (gain : (1 - s - 2 * s ^ 2) * density F * density G ≤ density F' * density G')

noncomputable def fr_one_step_data {m a b : ℕ} {F G : Family (m + 1)} {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (ha : 0 < a) (hab : a ≤ b)
    (havoid : CrossAvoids a b F G) : FRStep s (a := a) (b := b) F G :=
  Classical.choice <| by
    rcases fr_one_step hs0 hs ha hab havoid with hshift | hsame | hwiden
    · obtain ⟨F', G', hav, hgain⟩ := hshift
      exact ⟨FRStep.shifted F' G' hav hgain⟩
    · obtain ⟨F', G', hav, hgain⟩ := hsame
      exact ⟨FRStep.same F' G' hav hgain⟩
    · obtain ⟨F', G', hav, hgain⟩ := hwiden
      exact ⟨FRStep.widened F' G' hav hgain⟩

/-- The data carried by a complete iteration path.  `A` counts good steps,
`B` counts widening steps, and `d` counts the good steps which shift the
forbidden interval. -/
structure FRResult (s : ℝ) {m a b : ℕ} (F G : Family m) where
  m' : ℕ
  A : ℕ
  B : ℕ
  d : ℕ
  a' : ℕ
  b' : ℕ
  F' : Family m'
  G' : Family m'
  steps : m' + A + B = m
  shifts : d ≤ A
  upper : b' + d = b
  lower : a' + B + d = a
  interval : a' ≤ b' ∧ b' ≤ m'
  terminal : a' = 0 ∨ b' = m'
  avoids : CrossAvoids a' b' F' G'
  density_gain :
    (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * density F * density G ≤
      density F' * density G'

/-- Iterating `fr_one_step` must reach an endpoint of the interval. -/
noncomputable def fr_iterate {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    ∀ {m a b : ℕ} (F G : Family m), a ≤ b → b ≤ m → CrossAvoids a b F G →
      FRResult s (a := a) (b := b) F G := by
  have hq0 : 0 ≤ 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  intro m
  induction m with
  | zero =>
      intro a b F G hab hbm havoid
      have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      exact
        { m' := 0, A := 0, B := 0, d := 0, a' := a, b' := b
          F' := F, G' := G
          steps := by omega
          shifts := by omega
          upper := by omega
          lower := by omega
          interval := ⟨by omega, by omega⟩
          terminal := Or.inl ha0
          avoids := havoid
          density_gain := by simp }
  | succ k ih =>
      intro a b F G hab hbm havoid
      by_cases ha0 : a = 0
      · exact
          { m' := k + 1, A := 0, B := 0, d := 0, a' := a, b' := b
            F' := F, G' := G
            steps := by omega
            shifts := by omega
            upper := by omega
            lower := by omega
            interval := ⟨hab, hbm⟩
            terminal := Or.inl ha0
            avoids := havoid
            density_gain := by simp }
      by_cases hbm' : b = k + 1
      · exact
          { m' := k + 1, A := 0, B := 0, d := 0, a' := a, b' := b
            F' := F, G' := G
            steps := by omega
            shifts := by omega
            upper := by omega
            lower := by omega
            interval := ⟨hab, hbm⟩
            terminal := Or.inr hbm'
            avoids := havoid
            density_gain := by simp }
      have hak : 0 < a := Nat.pos_of_ne_zero ha0
      have hbk : b ≤ k := by omega
      rcases fr_one_step_data hs0 hs hak hab havoid with
        ⟨F1, G1, havoid1, hgain1⟩ | ⟨F1, G1, havoid1, hgain1⟩ |
          ⟨F1, G1, havoid1, hgain1⟩
      · have hab1 : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
        have hres := ih (a := a - 1) (b := b - 1) F1 G1 hab1 (by omega) havoid1
        exact
          { m' := hres.m', A := hres.A + 1, B := hres.B, d := hres.d + 1
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := by have h := hres.shifts; omega
            upper := by have h := hres.upper; omega
            lower := by have h := hres.lower; omega
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ (hres.A + 1) * (1 - s - 2 * s ^ 2) ^ hres.B *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 + s) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }
      · have hres := ih (a := a) (b := b) F1 G1 hab hbk havoid1
        exact
          { m' := hres.m', A := hres.A + 1, B := hres.B, d := hres.d
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := hres.shifts.trans (Nat.le_add_right _ _)
            upper := hres.upper
            lower := hres.lower
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ (hres.A + 1) * (1 - s - 2 * s ^ 2) ^ hres.B *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 + s) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }
      · have hab1 : a - 1 ≤ b := (Nat.sub_le a 1).trans hab
        have hres := ih (a := a - 1) (b := b) F1 G1 hab1 hbk havoid1
        exact
          { m' := hres.m', A := hres.A, B := hres.B + 1, d := hres.d
            a' := hres.a', b' := hres.b', F' := hres.F', G' := hres.G'
            steps := by have h := hres.steps; omega
            shifts := hres.shifts
            upper := hres.upper
            lower := by have h := hres.lower; omega
            interval := hres.interval
            terminal := hres.terminal
            avoids := hres.avoids
            density_gain := by
              calc
                (1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ (hres.B + 1) *
                      density F * density G =
                    ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      ((1 - s - 2 * s ^ 2) * density F * density G) := by
                        rw [pow_succ]
                        ring
                _ ≤ ((1 + s) ^ hres.A * (1 - s - 2 * s ^ 2) ^ hres.B) *
                      (density F1 * density G1) := by
                        gcongr
                _ ≤ density hres.F' * density hres.G' := by
                  simpa [mul_assoc] using hres.density_gain }

end Erdos703Iteration

/-! ### Upstream module `JSP573/External/Erdos703/McDiarmid.lean` -/

/-!
# A finite weighted McDiarmid inequality

This file proves bounded-differences concentration for an arbitrary finite product
distribution.  The coordinates may have different probability weights (and hence the
specialization to `Bool` includes independent, non-identically distributed biased coins).

The proof is finite and elementary apart from Hoeffding's lemma, for which we use the
proved theorem in Mathlib.  All probabilities below are represented explicitly as finite
weighted sums, so consumers do not have to set up measure-theoretic independence.
-/

namespace Erdos703McDiarmid

open _root_.Finset _root_.Function _root_.MeasureTheory _root_.ProbabilityTheory _root_.Real

attribute [local instance] Classical.propDecidable

noncomputable section

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The mass of a point in a finite product distribution. -/
def productMass {n : ℕ} (w : Fin n → α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ i, w i (x i)

/-- The (normalized, when the coordinate weights are normalized) weighted expectation. -/
def weightedMean {n : ℕ} (w : Fin n → α → ℝ) (f : (Fin n → α) → ℝ) : ℝ :=
  ∑ x, productMass w x * f x

/-- A finite probability measure associated to normalized real weights. -/
def finiteWeightMeasure (w : α → ℝ) : Measure α :=
  Measure.sum fun a ↦ ENNReal.ofReal (w a) • Measure.dirac a

omit [Nonempty α] [MeasurableSingletonClass α] in
lemma finiteWeightMeasure_isProbability (w : α → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) :
    IsProbabilityMeasure (finiteWeightMeasure w) := by
  unfold finiteWeightMeasure
  apply HasSum.isProbabilityMeasure_sum_dirac hw0
  simpa [hw1] using hasSum_fintype w

omit [Nonempty α] in
lemma integral_finiteWeightMeasure (w : α → ℝ) (hw0 : ∀ a, 0 ≤ w a)
    (g : α → ℝ) :
    ∫ a, g a ∂finiteWeightMeasure w = ∑ a, w a * g a := by
  rw [finiteWeightMeasure, integral_sum_dirac (by simp)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul, tsum_fintype]

/-- Hoeffding's lemma for a finite normalized weighted sum. -/
lemma finite_weighted_hoeffding (w : α → ℝ) (g : α → ℝ) (lo hi lam : ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (hg : ∀ a, g a ∈ Set.Icc lo hi) :
    ∑ a, w a * exp (lam * (g a - ∑ z, w z * g z)) ≤
      exp (((hi - lo) / 2) ^ 2 * lam ^ 2 / 2) := by
  let μ := finiteWeightMeasure w
  let : IsProbabilityMeasure μ := finiteWeightMeasure_isProbability w hw0 hw1
  have hmeas : AEMeasurable g μ := AEMeasurable.of_discrete
  have hmem : ∀ᵐ a ∂μ, g a ∈ Set.Icc lo hi := Filter.Eventually.of_forall hg
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ) hmeas hmem
  have hmgf := hsub.mgf_le lam
  rw [mgf, integral_finiteWeightMeasure w hw0] at hmgf
  rw [integral_finiteWeightMeasure w hw0] at hmgf
  have hlohi : lo ≤ hi := by
    let a : α := Classical.choice (inferInstance : Nonempty α)
    exact (hg a).1.trans (hg a).2
  simpa [μ, abs_of_nonneg (sub_nonneg.mpr hlohi)] using hmgf

/-- Hoeffding's lemma in the form useful for bounded differences: only the pairwise
oscillation of the finite random variable is specified. -/
lemma finite_weighted_hoeffding_of_pairwise (w : α → ℝ) (g : α → ℝ) (b lam : ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) (hb : 0 ≤ b)
    (hosc : ∀ a z, |g a - g z| ≤ b) :
    ∑ a, w a * exp (lam * (g a - ∑ z, w z * g z)) ≤
      exp (b ^ 2 * lam ^ 2 / 8) := by
  let S : Finset ℝ := Finset.univ.image g
  have hS : S.Nonempty := by
    let a : α := Classical.choice (inferInstance : Nonempty α)
    exact ⟨g a, Finset.mem_image_of_mem g (Finset.mem_univ a)⟩
  let lo : ℝ := S.min' hS
  let hi : ℝ := S.max' hS
  have hgIcc : ∀ a, g a ∈ Set.Icc lo hi := by
    intro a
    exact ⟨Finset.min'_le S (g a) (Finset.mem_image_of_mem g (Finset.mem_univ a)),
      Finset.le_max' S (g a) (Finset.mem_image_of_mem g (Finset.mem_univ a))⟩
  have hwidth0 : 0 ≤ hi - lo := sub_nonneg.mpr (Finset.min'_le_max' S hS)
  have hwidth : hi - lo ≤ b := by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
    dsimp [hi, lo]
    rw [← ha, ← hz]
    exact (le_abs_self (g a - g z)).trans (hosc a z)
  refine (finite_weighted_hoeffding w g lo hi lam hw0 hw1 hgIcc).trans ?_
  apply Real.exp_le_exp.mpr
  have hsquare : (hi - lo) ^ 2 ≤ b ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsquare (sq_nonneg lam)
  nlinarith

/-! ## Finite product identities -/

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma sum_fin_succ_eq {n : ℕ} {β : Type*} [AddCommMonoid β]
    (F : (Fin (n + 1) → α) → β) :
    ∑ x, F x = ∑ a : α, ∑ y : Fin n → α, F (Fin.cons a y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) ↦ α)).sum_comp]
  exact Fintype.sum_prod_type _

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp] lemma productMass_cons {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (a : α) (y : Fin n → α) :
    productMass w (Fin.cons a y) =
      w 0 a * productMass (fun i z ↦ w i.succ z) y := by
  simp [productMass, Fin.prod_univ_succ]

/-- Average over the first coordinate, retaining the remaining coordinates. -/
def sectionAverage {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) (y : Fin n → α) : ℝ :=
  ∑ a, w 0 a * f (Fin.cons a y)

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma weightedMean_succ {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) :
    weightedMean w f =
      weightedMean (fun i z ↦ w i.succ z) (sectionAverage w f) := by
  simp only [weightedMean, sum_fin_succ_eq, productMass_cons, sectionAverage]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma sectionAverage_boundedDiff {n : ℕ} (w : Fin (n + 1) → α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ) (b : Fin (n + 1) → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hbd : ∀ i (x y : Fin (n + 1) → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i) :
    ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) →
      |sectionAverage w f x - sectionAverage w f y| ≤ b i.succ := by
  intro i x y hxy
  rw [sectionAverage, sectionAverage, ← Finset.sum_sub_distrib]
  calc
    |∑ a, (w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y))|
        ≤ ∑ a, |w 0 a * f (Fin.cons a x) - w 0 a * f (Fin.cons a y)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, w 0 a * |f (Fin.cons a x) - f (Fin.cons a y)| := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw0 0 a)]
    _ ≤ ∑ a, w 0 a * b i.succ := by
          apply Finset.sum_le_sum
          intro a _
          apply mul_le_mul_of_nonneg_left _ (hw0 0 a)
          apply hbd i.succ
          intro j hj
          cases j using Fin.cases with
          | zero => rfl
          | succ j =>
              exact hxy j (fun h ↦ hj (congrArg (fun k : Fin n ↦ k.succ) h))
    _ = b i.succ := by rw [← Finset.sum_mul, hw1]; simp

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma productMass_nonneg {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (x : Fin n → α) :
    0 ≤ productMass w x := by
  exact Finset.prod_nonneg fun i _ ↦ hw0 i (x i)

/-! ## Exponential moments and the tail bound -/

/-- The centered exponential-moment estimate behind McDiarmid's inequality. -/
theorem expMomentBound (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (lam : ℝ) :
    ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) ≤
      exp (lam ^ 2 / 8 * ∑ i, b i ^ 2) := by
  induction n with
  | zero => simp [productMass, weightedMean]
  | succ n ih =>
      let wt : Fin n → α → ℝ := fun i a ↦ w i.succ a
      let g : (Fin n → α) → ℝ := sectionAverage w f
      let μ : ℝ := weightedMean w f
      have hmean : weightedMean wt g = μ := by
        exact (weightedMean_succ w f).symm
      have hi := ih wt g (fun i ↦ b i.succ)
        (fun i a ↦ hw0 i.succ a) (fun i ↦ hw1 i.succ) (fun i ↦ hb i.succ)
        (sectionAverage_boundedDiff w f b hw0 hw1 hbd)
      rw [hmean] at hi
      have hsection (y : Fin n → α) :
          ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) ≤
            exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ)) := by
        have hosc : ∀ a z : α,
            |f (Fin.cons a y) - f (Fin.cons z y)| ≤ b 0 := by
          intro a z
          apply hbd 0
          intro j hj
          cases j using Fin.cases with
          | zero => exact (hj rfl).elim
          | succ j => rfl
        have hh := finite_weighted_hoeffding_of_pairwise
          (w 0) (fun a ↦ f (Fin.cons a y)) (b 0) lam
          (hw0 0) (hw1 0) (hb 0) hosc
        have hfactor :
            ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) =
              exp (lam * (g y - μ)) *
                ∑ a, w 0 a * exp
                  (lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          have hexp :
              lam * (f (Fin.cons a y) - μ) =
                lam * (g y - μ) +
                  lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y)) := by
            dsimp [g, sectionAverage]
            ring
          rw [hexp, Real.exp_add]
          ring
        rw [hfactor]
        calc
          exp (lam * (g y - μ)) *
                ∑ a, w 0 a * exp
                  (lam * (f (Fin.cons a y) - ∑ z, w 0 z * f (Fin.cons z y)))
              ≤ exp (lam * (g y - μ)) * exp (b 0 ^ 2 * lam ^ 2 / 8) :=
                mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
          _ = exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ)) := by ring
      calc
        ∑ x, productMass w x * exp (lam * (f x - weightedMean w f))
            = ∑ y, productMass wt y *
                ∑ a, w 0 a * exp (lam * (f (Fin.cons a y) - μ)) := by
              rw [sum_fin_succ_eq, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              rw [productMass_cons]
              dsimp [wt, μ]
              ring
        _ ≤ ∑ y, productMass wt y *
              (exp (b 0 ^ 2 * lam ^ 2 / 8) * exp (lam * (g y - μ))) := by
              apply Finset.sum_le_sum
              intro y _
              exact mul_le_mul_of_nonneg_left (hsection y)
                (productMass_nonneg wt (fun i a ↦ hw0 i.succ a) y)
        _ = exp (b 0 ^ 2 * lam ^ 2 / 8) *
              ∑ y, productMass wt y * exp (lam * (g y - μ)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ ≤ exp (b 0 ^ 2 * lam ^ 2 / 8) *
              exp (lam ^ 2 / 8 * ∑ i : Fin n, b i.succ ^ 2) :=
              mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
        _ = exp (lam ^ 2 / 8 * ∑ i : Fin (n + 1), b i ^ 2) := by
              rw [← Real.exp_add, Fin.sum_univ_succ]
              congr 1
              ring

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma sum_productMass_eq_one (n : ℕ) (w : Fin n → α → ℝ)
    (hw1 : ∀ i, ∑ a, w i a = 1) :
    ∑ x, productMass w x = 1 := by
  induction n with
  | zero => simp [productMass]
  | succ n ih =>
      rw [sum_fin_succ_eq]
      simp_rw [productMass_cons, ← Finset.mul_sum]
      rw [← Finset.sum_mul, hw1 0]
      simp only [one_mul]
      simpa using ih (fun i a ↦ w i.succ a) (fun i ↦ hw1 i.succ)

/-- Weighted mass of an event in the finite product space. -/
def eventMass {n : ℕ} (w : Fin n → α → ℝ) (E : Set (Fin n → α)) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ x ∈ E), productMass w x

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma eventMass_univ {n : ℕ} (w : Fin n → α → ℝ)
    (hw1 : ∀ i, ∑ a, w i a = 1) :
    eventMass w Set.univ = 1 := by
  simp [eventMass, sum_productMass_eq_one n w hw1]

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma eventMass_mono {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) {E F : Set (Fin n → α)} (hEF : E ⊆ F) :
    eventMass w E ≤ eventMass w F := by
  unfold eventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hEF hx.2⟩
  · intro x _ _
    exact productMass_nonneg w hw0 x

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma eventMass_le_one {n : ℕ} (w : Fin n → α → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (E : Set (Fin n → α)) : eventMass w E ≤ 1 := by
  rw [← eventMass_univ w hw1]
  exact eventMass_mono w hw0 (Set.subset_univ E)

/-- Upper-tail McDiarmid inequality for an arbitrary normalized finite product distribution.
The positivity assumption merely excludes the degenerate all-zero bounded-difference budget. -/
theorem mcdiarmid_upper (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) (hS : 0 < ∑ i, b i ^ 2) :
    eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  let S : ℝ := ∑ i, b i ^ 2
  let lam : ℝ := 4 * t / S
  have hlam : 0 ≤ lam := div_nonneg (mul_nonneg (by norm_num) ht) hS.le
  have hpoint : ∀ x ∈ Finset.univ.filter
      (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
      productMass w x * exp (lam * t) ≤
        productMass w x * exp (lam * (f x - weightedMean w f)) := by
    intro x hx
    apply mul_le_mul_of_nonneg_left _ (productMass_nonneg w hw0 x)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hlam
    have hevent := (Finset.mem_filter.mp hx).2
    change weightedMean w f + t ≤ f x at hevent
    linarith
  have hmarkov :
      eventMass w {x | weightedMean w f + t ≤ f x} * exp (lam * t) ≤
        ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) := by
    calc
      eventMass w {x | weightedMean w f + t ≤ f x} * exp (lam * t)
          = ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
                productMass w x * exp (lam * t) := by
            simp only [eventMass, Finset.sum_mul]
      _ ≤ ∑ x ∈ Finset.univ.filter
              (fun x : Fin n → α ↦ x ∈ {x | weightedMean w f + t ≤ f x}),
                productMass w x * exp (lam * (f x - weightedMean w f)) := by
            exact Finset.sum_le_sum hpoint
      _ ≤ ∑ x, productMass w x * exp (lam * (f x - weightedMean w f)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro x _ _
            exact mul_nonneg (productMass_nonneg w hw0 x) (Real.exp_nonneg _)
  have hmom := expMomentBound n w f b hw0 hw1 hb hbd lam
  have hdiv : eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (lam ^ 2 / 8 * S) / exp (lam * t) := by
    rw [le_div_iff₀ (Real.exp_pos _)]
    exact hmarkov.trans (by simpa [S] using hmom)
  calc
    eventMass w {x | weightedMean w f + t ≤ f x}
        ≤ exp (lam ^ 2 / 8 * S) / exp (lam * t) := hdiv
    _ = exp (lam ^ 2 / 8 * S - lam * t) := by rw [Real.exp_sub]
    _ = exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
      congr 1
      dsimp [lam, S]
      field_simp
      ring

/-- Degenerate-safe upper-tail form.  When all difference bounds vanish, the event has
mass at most one, which is exactly the right-hand side under Lean's division-by-zero
convention. -/
theorem mcdiarmid_upper_all (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass w {x | weightedMean w f + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  have hnonneg : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  rcases hnonneg.eq_or_lt with hzero | hpos
  · have hzero' : ∑ i, b i ^ 2 = 0 := hzero.symm
    simpa [hzero'] using eventMass_le_one w hw0 hw1
      {x | weightedMean w f + t ≤ f x}
  · exact mcdiarmid_upper n w f b hw0 hw1 hb hbd t ht hpos

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp] lemma weightedMean_neg {n : ℕ} (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) :
    weightedMean w (fun x ↦ -f x) = -weightedMean w f := by
  simp only [weightedMean, mul_neg, Finset.sum_neg_distrib]

/-- Lower-tail McDiarmid inequality. -/
theorem mcdiarmid_lower_all (n : ℕ) (w : Fin n → α → ℝ)
    (f : (Fin n → α) → ℝ) (b : Fin n → ℝ)
    (hw0 : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hb : ∀ i, 0 ≤ b i)
    (hbd : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b i)
    (t : ℝ) (ht : 0 ≤ t) :
    eventMass w {x | f x ≤ weightedMean w f - t} ≤
      exp (-2 * t ^ 2 / ∑ i, b i ^ 2) := by
  have hbd_neg : ∀ i (x y : Fin n → α),
      (∀ j, j ≠ i → x j = y j) →
      |(-f x) - (-f y)| ≤ b i := by
    intro i x y hxy
    simpa only [neg_sub_neg, abs_neg] using
      hbd i y x (fun j hj ↦ (hxy j hj).symm)
  have h := mcdiarmid_upper_all n w (fun x ↦ -f x) b
    hw0 hw1 hb hbd_neg t ht
  have hset : {x | f x ≤ weightedMean w f - t} =
      {x | weightedMean w (fun x ↦ -f x) + t ≤ -f x} := by
    ext x
    simp only [Set.mem_ofPred_eq, weightedMean_neg]
    constructor <;> intro hx <;> linarith
  rw [hset]
  exact h

/-! ## Independent biased Bernoulli specialization -/

/-- Coordinate weights for independent Bernoulli bits, with `true` having probability `p i`. -/
def bernoulliWeight {n : ℕ} (p : Fin n → ℝ) (i : Fin n) (q : Bool) : ℝ :=
  if q then p i else 1 - p i

lemma bernoulliWeight_sum_one {n : ℕ} (p : Fin n → ℝ) :
    ∀ i, ∑ q : Bool, bernoulliWeight p i q = 1 := by
  intro i
  rw [Fintype.sum_bool]
  simp [bernoulliWeight]

end
end Erdos703McDiarmid

/-! ### Upstream module `JSP573/External/Erdos703/Endpoints.lean` -/

namespace Erdos703Endpoints

open _root_.Finset _root_.Real
open scoped BigOperators symmDiff

noncomputable section

abbrev Cube (n : ℕ) := Finset (Fin n)
abbrev Family (n : ℕ) := Finset (Cube n)
abbrev BoolCube (n : ℕ) := Fin n → Bool

def fairBias (n : ℕ) : Fin n → ℝ := fun _ ↦ 1 / 2

def fairWeight (n : ℕ) : Fin n → Bool → ℝ :=
  Erdos703McDiarmid.bernoulliWeight (fairBias n)

def boolSupport {n : ℕ} (x : BoolCube n) : Cube n :=
  Finset.univ.filter fun i ↦ x i = true

def boolIndicator {n : ℕ} (S : Cube n) : BoolCube n :=
  fun i ↦ decide (i ∈ S)

@[simp] lemma boolSupport_indicator {n : ℕ} (S : Cube n) :
    boolSupport (boolIndicator S) = S := by
  ext i
  simp [boolSupport, boolIndicator]

@[simp] lemma boolIndicator_support {n : ℕ} (x : BoolCube n) :
    boolIndicator (boolSupport x) = x := by
  funext i
  cases h : x i <;> simp [boolIndicator, boolSupport, h]

def boolFinsetEquiv (n : ℕ) : BoolCube n ≃ Cube n where
  toFun := boolSupport
  invFun := boolIndicator
  left_inv := boolIndicator_support
  right_inv := boolSupport_indicator

lemma fairWeight_apply {n : ℕ} (i : Fin n) (b : Bool) :
    fairWeight n i b = 1 / 2 := by
  cases b <;> norm_num [fairWeight, fairBias, Erdos703McDiarmid.bernoulliWeight]

lemma fair_productMass {n : ℕ} (x : BoolCube n) :
    Erdos703McDiarmid.productMass (fairWeight n) x = (1 / 2 : ℝ) ^ n := by
  simp [Erdos703McDiarmid.productMass, fairWeight_apply]

def density {n : ℕ} (A : Family n) : ℝ :=
  (A.card : ℝ) / (2 : ℝ) ^ n

def cubeMean {n : ℕ} (f : Cube n → ℝ) : ℝ :=
  (∑ S ∈ (Finset.univ : Cube n).powerset, f S) / (2 : ℝ) ^ n

lemma fair_weightedMean_support {n : ℕ} (f : Cube n → ℝ) :
    Erdos703McDiarmid.weightedMean (fairWeight n) (fun x ↦ f (boolSupport x)) =
      cubeMean f := by
  unfold Erdos703McDiarmid.weightedMean cubeMean
  simp_rw [fair_productMass]
  have hsum : (∑ x : BoolCube n, (1 / 2 : ℝ) ^ n * f (boolSupport x)) =
      ∑ S : Cube n, (1 / 2 : ℝ) ^ n * f S := by
    simpa [boolFinsetEquiv] using
      (boolFinsetEquiv n).sum_comp (fun S ↦ (1 / 2 : ℝ) ^ n * f S)
  rw [hsum]
  have hpowerset : (Finset.univ : Cube n).powerset =
      (Finset.univ : Finset (Cube n)) := by
    ext S
    simp
  rw [hpowerset]
  simp only [one_div, inv_pow, mul_comm]
  rw [← Finset.sum_mul, div_eq_mul_inv]

lemma fair_eventMass_support {n : ℕ} (E : Family n) :
    Erdos703McDiarmid.eventMass (fairWeight n) {x | boolSupport x ∈ E} = density E := by
  unfold Erdos703McDiarmid.eventMass density
  rw [Finset.sum_filter]
  simp_rw [fair_productMass]
  have hsum : (∑ x : BoolCube n,
      if x ∈ {x | boolSupport x ∈ E} then (1 / 2 : ℝ) ^ n else 0) =
      ∑ S : Cube n, if S ∈ E then (1 / 2 : ℝ) ^ n else 0 := by
    simpa [boolFinsetEquiv] using
      (boolFinsetEquiv n).sum_comp
        (fun S : Cube n ↦ if S ∈ E then (1 / 2 : ℝ) ^ n else 0)
  rw [hsum]
  simp [div_eq_mul_inv, inv_pow]

def hamming {n : ℕ} (S T : Cube n) : ℕ := #(S ∆ T)

def OneLipschitz {n : ℕ} (f : Cube n → ℝ) : Prop :=
  ∀ S T, |f S - f T| ≤ hamming S T

/-- The exact black-box form of the two one-sided cube McDiarmid estimates
used by the endpoint arguments. -/
structure CubeMcDiarmid (n : ℕ) : Prop where
  upper : ∀ (f : Cube n → ℝ), OneLipschitz f → ∀ a : ℝ, cubeMean f = a →
    ∀ u : ℝ, 0 ≤ u → ∀ E : Family n,
      (∀ S ∈ E, a + u ≤ f S) →
      density E ≤ Real.exp (-2 * u ^ 2 / n)
  lower : ∀ (f : Cube n → ℝ), OneLipschitz f → ∀ a : ℝ, cubeMean f = a →
    ∀ u : ℝ, 0 ≤ u → ∀ E : Family n,
      (∀ S ∈ E, f S ≤ a - u) →
      density E ≤ Real.exp (-2 * u ^ 2 / n)

lemma hamming_support_le_one_of_off_eq {n : ℕ} (i : Fin n) (x y : BoolCube n)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    hamming (boolSupport x) (boolSupport y) ≤ 1 := by
  unfold hamming
  calc
    #(boolSupport x ∆ boolSupport y) ≤ #({i} : Finset (Fin n)) := by
      apply card_le_card
      intro j hj
      have hji : j = i := by
        by_contra hne
        have heq := hxy j hne
        have hmem : (j ∈ boolSupport x ↔ j ∈ boolSupport y) := by
          simp [boolSupport, heq]
        rcases mem_symmDiff.mp hj with h | h
        · exact h.2 (hmem.mp h.1)
        · exact h.2 (hmem.mpr h.1)
      simp [hji]
    _ = 1 := card_singleton i

lemma fairWeight_nonneg {n : ℕ} : ∀ i : Fin n, ∀ b : Bool, 0 ≤ fairWeight n i b := by
  intro i b
  rw [fairWeight_apply]
  norm_num

lemma fairWeight_sum_one {n : ℕ} : ∀ i : Fin n, ∑ b : Bool, fairWeight n i b = 1 := by
  intro i
  simp [fairWeight_apply]

/-- McDiarmid on the fair Boolean cube, transported through the characteristic-function
equivalence between subsets of `Fin n` and Boolean words. -/
theorem fairCubeMcDiarmid (n : ℕ) : CubeMcDiarmid n where
  upper := by
    intro f hf a hmean u hu E hE
    let fb : BoolCube n → ℝ := fun x ↦ f (boolSupport x)
    have hbd : ∀ i (x y : BoolCube n),
        (∀ j, j ≠ i → x j = y j) → |fb x - fb y| ≤ (1 : ℝ) := by
      intro i x y hxy
      exact (hf (boolSupport x) (boolSupport y)).trans (by
        exact_mod_cast hamming_support_le_one_of_off_eq i x y hxy)
    have hm := Erdos703McDiarmid.mcdiarmid_upper_all n (fairWeight n) fb
      (fun _ ↦ (1 : ℝ)) fairWeight_nonneg fairWeight_sum_one (fun _ ↦ by norm_num)
      hbd u hu
    calc
      density E = Erdos703McDiarmid.eventMass (fairWeight n)
          {x | boolSupport x ∈ E} := (fair_eventMass_support E).symm
      _ ≤ Erdos703McDiarmid.eventMass (fairWeight n)
          {x | Erdos703McDiarmid.weightedMean (fairWeight n) fb + u ≤ fb x} := by
        apply Erdos703McDiarmid.eventMass_mono (fairWeight n) fairWeight_nonneg
        intro x hx
        change boolSupport x ∈ E at hx
        change Erdos703McDiarmid.weightedMean (fairWeight n) fb + u ≤ fb x
        rw [show Erdos703McDiarmid.weightedMean (fairWeight n) fb = cubeMean f by
          exact fair_weightedMean_support f, hmean]
        exact hE (boolSupport x) hx
      _ ≤ Real.exp (-2 * u ^ 2 / n) := by
        simpa using hm

  lower := by
    intro f hf a hmean u hu E hE
    let fb : BoolCube n → ℝ := fun x ↦ f (boolSupport x)
    have hbd : ∀ i (x y : BoolCube n),
        (∀ j, j ≠ i → x j = y j) → |fb x - fb y| ≤ (1 : ℝ) := by
      intro i x y hxy
      exact (hf (boolSupport x) (boolSupport y)).trans (by
        exact_mod_cast hamming_support_le_one_of_off_eq i x y hxy)
    have hm := Erdos703McDiarmid.mcdiarmid_lower_all n (fairWeight n) fb
      (fun _ ↦ (1 : ℝ)) fairWeight_nonneg fairWeight_sum_one (fun _ ↦ by norm_num)
      hbd u hu
    calc
      density E = Erdos703McDiarmid.eventMass (fairWeight n)
          {x | boolSupport x ∈ E} := (fair_eventMass_support E).symm
      _ ≤ Erdos703McDiarmid.eventMass (fairWeight n)
          {x | fb x ≤ Erdos703McDiarmid.weightedMean (fairWeight n) fb - u} := by
        apply Erdos703McDiarmid.eventMass_mono (fairWeight n) fairWeight_nonneg
        intro x hx
        change boolSupport x ∈ E at hx
        change fb x ≤ Erdos703McDiarmid.weightedMean (fairWeight n) fb - u
        rw [show Erdos703McDiarmid.weightedMean (fairWeight n) fb = cubeMean f by
          exact fair_weightedMean_support f, hmean]
        exact hE (boolSupport x) hx
      _ ≤ Real.exp (-2 * u ^ 2 / n) := by
        simpa using hm

/-- The mean of one coordinate indicator under a product of Bernoulli weights. -/
theorem weightedMean_bit_true {n : ℕ} (p : Fin n → ℝ) (i : Fin n) :
    Erdos703McDiarmid.weightedMean (Erdos703McDiarmid.bernoulliWeight p)
      (fun x : BoolCube n ↦ if x i = true then 1 else 0) = p i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [Erdos703McDiarmid.weightedMean_succ]
          have hsection :
              Erdos703McDiarmid.sectionAverage
                (Erdos703McDiarmid.bernoulliWeight p)
                (fun x : BoolCube (n + 1) ↦
                  if x 0 = true then (1 : ℝ) else 0) =
                fun _ : BoolCube n ↦ p 0 := by
            funext y
            simp [Erdos703McDiarmid.sectionAverage,
              Erdos703McDiarmid.bernoulliWeight]
          rw [hsection]
          simp only [Erdos703McDiarmid.weightedMean]
          rw [← Finset.sum_mul,
            Erdos703McDiarmid.sum_productMass_eq_one n
              (fun i z ↦ Erdos703McDiarmid.bernoulliWeight p i.succ z)
              (fun i ↦ Erdos703McDiarmid.bernoulliWeight_sum_one p i.succ)]
          simp
      | succ i =>
          rw [Erdos703McDiarmid.weightedMean_succ]
          have hsection :
              Erdos703McDiarmid.sectionAverage
                (Erdos703McDiarmid.bernoulliWeight p)
                (fun x : BoolCube (n + 1) ↦
                  if x i.succ = true then (1 : ℝ) else 0) =
                fun x : BoolCube n ↦ if x i = true then 1 else 0 := by
            funext y
            simp [Erdos703McDiarmid.sectionAverage,
              Erdos703McDiarmid.bernoulliWeight]
          rw [hsection]
          exact ih (fun q ↦ p q.succ) i

lemma card_boolSupport_eq_sum {n : ℕ} (x : BoolCube n) :
    (#(boolSupport x) : ℝ) = ∑ i : Fin n, if x i = true then 1 else 0 := by
  rw [show (#(boolSupport x) : ℝ) = ∑ _i ∈ boolSupport x, (1 : ℝ) by
    rw [Finset.sum_const, nsmul_eq_mul]
    norm_num]
  rw [boolSupport, Finset.sum_filter]

lemma fair_weightedMean_card_support (n : ℕ) :
    Erdos703McDiarmid.weightedMean (fairWeight n)
      (fun x : BoolCube n ↦ (#(boolSupport x) : ℝ)) = (n : ℝ) / 2 := by
  simp_rw [card_boolSupport_eq_sum]
  simp only [Erdos703McDiarmid.weightedMean, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin n, ∑ x : BoolCube n,
        Erdos703McDiarmid.productMass (fairWeight n) x *
          (if x i = true then 1 else 0)) = ∑ i : Fin n, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hbit := weightedMean_bit_true (fairBias n) i
      change (∑ x : BoolCube n,
        Erdos703McDiarmid.productMass (fairWeight n) x *
          (if x i = true then 1 else 0)) = fairBias n i at hbit
      simpa only [fairBias] using hbit
    _ = (n : ℝ) / 2 := by
      simp only [one_div, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [div_eq_mul_inv]

lemma cubeMean_card (n : ℕ) :
    cubeMean (fun S : Cube n ↦ (#S : ℝ)) = (n : ℝ) / 2 := by
  rw [← fair_weightedMean_support]
  exact fair_weightedMean_card_support n

lemma density_nonneg {n : ℕ} (A : Family n) : 0 ≤ density A := by
  unfold density
  positivity

lemma density_le_one {n : ℕ} (A : Family n) : density A ≤ 1 := by
  unfold density
  rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
  norm_cast
  simpa using card_le_card (show A ⊆ (Finset.univ : Cube n).powerset by simp)

lemma hamming_comm {n : ℕ} (S T : Cube n) : hamming S T = hamming T S := by
  simp [hamming, symmDiff_comm]

lemma hamming_self {n : ℕ} (S : Cube n) : hamming S S = 0 := by
  simp [hamming]

lemma hamming_triangle {n : ℕ} (S T U : Cube n) :
    hamming S U ≤ hamming S T + hamming T U := by
  unfold hamming
  calc
    #(S ∆ U) ≤ #((S ∆ T) ∪ (T ∆ U)) :=
      card_le_card (show S ∆ U ⊆ (S ∆ T) ∪ (T ∆ U) from symmDiff_triangle S T U)
    _ ≤ #(S ∆ T) + #(T ∆ U) := card_union_le _ _

def familyDist {n : ℕ} (A : Family n) (hA : A.Nonempty) (S : Cube n) : ℕ :=
  A.inf' hA (fun T ↦ hamming S T)

lemma familyDist_eq_zero_of_mem {n : ℕ} {A : Family n} (hA : A.Nonempty)
    {S : Cube n} (hS : S ∈ A) : familyDist A hA S = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (Finset.inf'_le _ hS).trans_eq (hamming_self S)

lemma familyDist_triangle_right {n : ℕ} {A : Family n} (hA : A.Nonempty)
    (S T : Cube n) :
    familyDist A hA S ≤ hamming S T + familyDist A hA T := by
  obtain ⟨U, hU, hmin⟩ := Finset.exists_mem_eq_inf' hA (fun U ↦ hamming T U)
  unfold familyDist
  rw [hmin]
  exact (Finset.inf'_le _ hU).trans (hamming_triangle S T U)

lemma familyDist_lipschitz {n : ℕ} {A : Family n} (hA : A.Nonempty) :
    OneLipschitz (fun S ↦ (familyDist A hA S : ℝ)) := by
  intro S T
  rw [abs_le]
  constructor
  · have h := familyDist_triangle_right hA T S
    rw [hamming_comm T S] at h
    have hc : (familyDist A hA T : ℝ) ≤
        (hamming S T : ℝ) + familyDist A hA S := by exact_mod_cast h
    dsimp
    linarith
  · have h := familyDist_triangle_right hA S T
    have hc : (familyDist A hA S : ℝ) ≤
        (hamming S T : ℝ) + familyDist A hA T := by exact_mod_cast h
    dsimp
    linarith

lemma familyDist_mean_nonneg {n : ℕ} {A : Family n} (hA : A.Nonempty) :
    0 ≤ cubeMean (fun S ↦ (familyDist A hA S : ℝ)) := by
  unfold cubeMean
  positivity

/-- Finite-cube separated-families endpoint, conditional only on the generic
McDiarmid estimate above. -/
theorem separated_families {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (A B : Family n) (t : ℝ) (ht : 0 ≤ t)
    (hsep : ∀ S ∈ A, ∀ T ∈ B, t ≤ hamming S T) :
    density A * density B ≤ Real.exp (-t ^ 2 / n) := by
  by_cases hAe : A = ∅
  · simp [hAe, density, Real.exp_nonneg]
  by_cases hBe : B = ∅
  · simp [hBe, density, Real.exp_nonneg]
  have hA : A.Nonempty := nonempty_iff_ne_empty.mpr hAe
  have hB : B.Nonempty := nonempty_iff_ne_empty.mpr hBe
  let f : Cube n → ℝ := fun S ↦ (familyDist A hA S : ℝ)
  let a : ℝ := cubeMean f
  have ha0 : 0 ≤ a := familyDist_mean_nonneg hA
  have hf : OneLipschitz f := familyDist_lipschitz hA
  have hfA : ∀ S ∈ A, f S = 0 := by
    intro S hS
    simp [f, familyDist_eq_zero_of_mem hA hS]
  have hfB : ∀ S ∈ B, t ≤ f S := by
    intro S hS
    have hnat : ∀ T ∈ A, t ≤ (hamming S T : ℝ) := by
      intro T hT
      simpa [hamming_comm] using hsep T hT S hS
    obtain ⟨u, hu, hmin⟩ := Finset.exists_mem_eq_inf' hA (fun T ↦ hamming S T)
    dsimp [f]
    unfold familyDist
    rw [hmin]
    exact hnat u hu
  by_cases hat : t ≤ a
  · have hlow : density A ≤ Real.exp (-2 * a ^ 2 / n) := by
      apply mc.lower f hf a rfl a ha0 A
      intro S hS
      rw [hfA S hS]
      linarith
    calc
      density A * density B ≤ density A * 1 :=
        mul_le_mul_of_nonneg_left (density_le_one B) (density_nonneg A)
      _ = density A := by ring
      _ ≤ Real.exp (-2 * a ^ 2 / n) := hlow
      _ ≤ Real.exp (-t ^ 2 / n) := by
        apply Real.exp_le_exp.mpr
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        apply (div_le_div_iff_of_pos_right hnR).mpr
        nlinarith [sq_nonneg a, sq_nonneg t]
  · have hat' : a < t := lt_of_not_ge hat
    have hu : 0 ≤ t - a := sub_nonneg.mpr hat'.le
    have hlow : density A ≤ Real.exp (-2 * a ^ 2 / n) := by
      apply mc.lower f hf a rfl a ha0 A
      intro S hS
      rw [hfA S hS]
      linarith
    have hupp : density B ≤ Real.exp (-2 * (t - a) ^ 2 / n) := by
      apply mc.upper f hf a rfl (t - a) hu B
      intro S hS
      simpa only [add_sub_cancel] using hfB S hS
    calc
      density A * density B ≤
          Real.exp (-2 * a ^ 2 / n) * Real.exp (-2 * (t - a) ^ 2 / n) :=
        mul_le_mul hlow hupp (density_nonneg B) (Real.exp_nonneg _)
      _ = Real.exp ((-2 * a ^ 2 / n) + (-2 * (t - a) ^ 2 / n)) := by
        rw [← Real.exp_add]
      _ ≤ Real.exp (-t ^ 2 / n) := by
        apply Real.exp_le_exp.mpr
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        rw [← add_div]
        apply (div_le_div_iff_of_pos_right hnR).mpr
        nlinarith [sq_nonneg (2 * a - t)]

def cubeCompl {n : ℕ} (S : Cube n) : Cube n := Finset.univ \ S

lemma cubeCompl_involutive {n : ℕ} (S : Cube n) : cubeCompl (cubeCompl S) = S := by
  ext i
  simp [cubeCompl]

lemma cubeCompl_injective {n : ℕ} : Function.Injective (cubeCompl : Cube n → Cube n) := by
  intro S T h
  simpa only [cubeCompl_involutive] using congrArg cubeCompl h

def complementFamily {n : ℕ} (B : Family n) : Family n := B.image cubeCompl

lemma complementFamily_density {n : ℕ} (B : Family n) :
    density (complementFamily B) = density B := by
  unfold density complementFamily
  rw [card_image_of_injective _ cubeCompl_injective]

lemma inter_subset_symmDiff_compl {n : ℕ} (S T : Cube n) :
    S ∩ T ⊆ S ∆ cubeCompl T := by
  intro i hi
  rw [mem_symmDiff]
  exact Or.inl ⟨(mem_inter.mp hi).1, by simp [cubeCompl, (mem_inter.mp hi).2]⟩

/-- Large cross intersections reduce to separated families after complementing
the second family. -/
theorem cross_high {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (A B : Family n) (t : ℝ) (ht : 0 ≤ t)
    (hcross : ∀ S ∈ A, ∀ T ∈ B, t ≤ #(S ∩ T)) :
    density A * density B ≤ Real.exp (-t ^ 2 / n) := by
  have hsep : ∀ S ∈ A, ∀ U ∈ complementFamily B, t ≤ hamming S U := by
    intro S hS U hU
    rw [complementFamily, mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    exact (hcross S hS T hT).trans (by
      exact_mod_cast card_le_card (inter_subset_symmDiff_compl S T))
  rw [← complementFamily_density B]
  exact separated_families hn mc A (complementFamily B) t ht hsep

lemma card_oneLipschitz {n : ℕ} : OneLipschitz (fun S : Cube n ↦ (#S : ℝ)) := by
  intro S T
  have hST := hamming_triangle S T ∅
  have hTS := hamming_triangle T S ∅
  have hzero (U : Cube n) : hamming U ∅ = #U := by
    simp [hamming, symmDiff_def]
  have hST' : #S ≤ hamming S T + #T := by simpa [hzero] using hST
  have hTS' : #T ≤ hamming T S + #S := by simpa [hzero] using hTS
  rw [abs_le]
  constructor
  · have hc : (#T : ℝ) ≤ (hamming S T : ℝ) + #S := by
      rw [hamming_comm]
      exact_mod_cast hTS'
    linarith
  · have hc : (#S : ℝ) ≤ (hamming S T : ℝ) + #T := by exact_mod_cast hST'
    linarith

lemma density_filter_add_filter_not {n : ℕ} (A : Family n) (p : Cube n → Prop)
    [DecidablePred p] [∀ S, Decidable (¬p S)] :
    density (A.filter p) + density (A.filter fun S ↦ ¬p S) = density A := by
  unfold density
  rw [← add_div, ← Nat.cast_add, card_filter_add_card_filter_not]

/-- Small cross intersections endpoint.  `hcardMean` is the elementary
identity saying that a uniform random subset has expected cardinality `n/2`;
it is kept explicit so that the only analytic input is `CubeMcDiarmid`. -/
theorem cross_low {n : ℕ} (hn : 0 < n) (mc : CubeMcDiarmid n)
    (hcardMean : cubeMean (fun S : Cube n ↦ (#S : ℝ)) = (n : ℝ) / 2)
    (A B : Family n) (κ : ℝ) (hκ0 : 0 < κ)
    (hcross : ∀ S ∈ A, ∀ T ∈ B,
      (#(S ∩ T) : ℝ) < (1 / 2 - κ) * n) :
    density A * density B ≤
      max (2 * Real.exp (-(κ ^ 2 * n) / 2))
        (4 * Real.exp (-(κ ^ 2 * n) / 4)) := by
  let large : Cube n → Prop := fun S ↦ (1 / 2 - κ / 2) * n ≤ (#S : ℝ)
  let Astar : Family n := A.filter large
  let Bstar : Family n := B.filter large
  let Alow : Family n := A.filter fun S ↦ ¬ large S
  let Blow : Family n := B.filter fun S ↦ ¬ large S
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu : 0 ≤ κ * n / 2 := by positivity
  have hAlow : density Alow ≤ Real.exp (-(κ ^ 2 * n) / 2) := by
    have h := mc.lower (fun S : Cube n ↦ (#S : ℝ)) card_oneLipschitz
      ((n : ℝ) / 2) hcardMean (κ * n / 2) hu Alow
    have hevent : ∀ S ∈ Alow, (#S : ℝ) ≤ (n : ℝ) / 2 - κ * n / 2 := by
      intro S hS
      have hs := (mem_filter.mp hS).2
      dsimp [large] at hs
      push Not at hs
      linarith
    have hh := h hevent
    calc
      density Alow ≤ Real.exp (-2 * (κ * n / 2) ^ 2 / n) := hh
      _ = Real.exp (-(κ ^ 2 * n) / 2) := by
        congr 1
        field_simp [ne_of_gt hnR]
  have hBlow : density Blow ≤ Real.exp (-(κ ^ 2 * n) / 2) := by
    have h := mc.lower (fun S : Cube n ↦ (#S : ℝ)) card_oneLipschitz
      ((n : ℝ) / 2) hcardMean (κ * n / 2) hu Blow
    have hevent : ∀ S ∈ Blow, (#S : ℝ) ≤ (n : ℝ) / 2 - κ * n / 2 := by
      intro S hS
      have hs := (mem_filter.mp hS).2
      dsimp [large] at hs
      push Not at hs
      linarith
    have hh := h hevent
    calc
      density Blow ≤ Real.exp (-2 * (κ * n / 2) ^ 2 / n) := hh
      _ = Real.exp (-(κ ^ 2 * n) / 2) := by
        congr 1
        field_simp [ne_of_gt hnR]
  have hApart : density Astar + density Alow = density A := by
    exact density_filter_add_filter_not A large
  have hBpart : density Bstar + density Blow = density B := by
    exact density_filter_add_filter_not B large
  by_cases hAdense : density A ≤ 2 * density Astar
  swap
  · have hAupper : density A ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := by
      have hstarlt : density Astar < density Alow := by
        rw [← hApart] at hAdense
        push Not at hAdense
        linarith
      rw [← hApart]
      linarith
    calc
      density A * density B ≤ density A * 1 :=
        mul_le_mul_of_nonneg_left (density_le_one B) (density_nonneg A)
      _ = density A := by ring
      _ ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := hAupper
      _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
          (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_left _ _
  by_cases hBdense : density B ≤ 2 * density Bstar
  swap
  · have hBupper : density B ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := by
      have hstarlt : density Bstar < density Blow := by
        rw [← hBpart] at hBdense
        push Not at hBdense
        linarith
      rw [← hBpart]
      linarith
    calc
      density A * density B ≤ 1 * density B :=
        mul_le_mul_of_nonneg_right (density_le_one A) (density_nonneg B)
      _ = density B := by ring
      _ ≤ 2 * Real.exp (-(κ ^ 2 * n) / 2) := hBupper
      _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
          (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_left _ _
  have hstarCross : ∀ S ∈ Astar, ∀ U ∈ complementFamily Bstar,
      κ * n / 2 ≤ (#(S ∩ U) : ℝ) := by
    intro S hS U hU
    rw [complementFamily, mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    have hSA := (mem_filter.mp hS)
    have hTB := (mem_filter.mp hT)
    have hi := hcross S hSA.1 T hTB.1
    have hsLarge := hSA.2
    dsimp [large] at hsLarge
    have hcardDiff : #(S \ T) + #(S ∩ T) = #S := by
      exact card_sdiff_add_card_inter S T
    have hEq : S ∩ cubeCompl T = S \ T := by
      ext i
      simp [cubeCompl]
    rw [hEq]
    have hcardDiffR : (#(S \ T) : ℝ) + #(S ∩ T) = #S := by exact_mod_cast hcardDiff
    linarith
  have hhigh := cross_high hn mc Astar (complementFamily Bstar)
    (κ * n / 2) hu hstarCross
  rw [complementFamily_density] at hhigh
  have hprod : density A * density B ≤ 4 * (density Astar * density Bstar) := by
    calc
      density A * density B ≤
          (2 * density Astar) * (2 * density Bstar) :=
        mul_le_mul hAdense hBdense (density_nonneg B)
          (mul_nonneg (by norm_num) (density_nonneg Astar))
      _ = 4 * (density Astar * density Bstar) := by ring
  calc
    density A * density B ≤ 4 * (density Astar * density Bstar) := hprod
    _ ≤ 4 * Real.exp (-((κ * n / 2) ^ 2) / n) :=
      mul_le_mul_of_nonneg_left hhigh (by norm_num)
    _ = 4 * Real.exp (-(κ ^ 2 * n) / 4) := by
      congr 2
      field_simp
      ring
    _ ≤ max (2 * Real.exp (-(κ ^ 2 * n) / 2))
        (4 * Real.exp (-(κ ^ 2 * n) / 4)) := le_max_right _ _

end

end Erdos703Endpoints

/-! ### Upstream module `JSP573/External/Erdos703/FranklRodl.lean` -/

/-!
# The Frankl--Rödl iteration for Erdős Problem 703

This file combines the finite coordinate-section iteration with its two
McDiarmid endpoint estimates.  Everything is quantitative and finite.
-/

namespace Erdos703FranklRodl

open _root_.Nat _root_.Finset _root_.Real
noncomputable section

lemma log_one_add_lower {s : ℝ} (hs0 : 0 ≤ s) :
    s - s ^ 2 ≤ Real.log (1 + s) := by
  have hpos : 0 < 1 + s := by linarith
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have heq : 1 - (1 + s)⁻¹ = s / (1 + s) := by
    field_simp [ne_of_gt hpos]
    ring
  rw [heq] at hbase
  have hfrac : s - s ^ 2 ≤ s / (1 + s) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [mul_nonneg hs0 (sq_nonneg s)]
  exact hfrac.trans hbase

lemma log_fr_bad_lower {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    -s - 4 * s ^ 2 ≤ Real.log (1 - s - 2 * s ^ 2) := by
  have hq : 0 < 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hbase := Real.one_sub_inv_le_log_of_pos hq
  have hcoef : 0 ≤ 1 - 6 * s - 8 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hpoly : 0 ≤ s ^ 2 * (1 - 6 * s - 8 * s ^ 2) :=
    mul_nonneg (sq_nonneg s) hcoef
  have hmul : (-s - 4 * s ^ 2) * (1 - s - 2 * s ^ 2) ≤ -(s + 2 * s ^ 2) := by
    nlinarith
  have heq : 1 - (1 - s - 2 * s ^ 2)⁻¹ =
      -(s + 2 * s ^ 2) / (1 - s - 2 * s ^ 2) := by
    apply (eq_div_iff hq.ne').2
    rw [sub_mul, one_mul, inv_mul_cancel₀ hq.ne']
    ring
  rw [heq] at hbase
  have hdiv : -s - 4 * s ^ 2 ≤
      -(s + 2 * s ^ 2) / (1 - s - 2 * s ^ 2) :=
    (le_div_iff₀ hq).2 hmul
  exact hdiv.trans hbase

lemma log_one_sub_sq_lower {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) :
    -2 * s ^ 2 ≤ Real.log (1 - s ^ 2) := by
  have hc : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hbase := Real.one_sub_inv_le_log_of_pos hc
  have hs_sq : s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self hs0 hs
  have hmul : (-2 * s ^ 2) * (1 - s ^ 2) ≤ -(s ^ 2) := by
    nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) (sq_nonneg s)]
  have heq : 1 - (1 - s ^ 2)⁻¹ = -(s ^ 2) / (1 - s ^ 2) := by
    field_simp [ne_of_gt hc]
    ring
  rw [heq] at hbase
  exact ((le_div_iff₀ hc).2 hmul).trans hbase

/-- The logarithmic bookkeeping behind equation (8) of Frankl--Rödl.
The deliberately generous constant `20` keeps the later arithmetic robust. -/
lemma good_bad_balance {n A B : ℕ} {s p pstar : ℝ}
    (hs0 : 0 < s) (hs : s ≤ 1 / 10) (hsteps : A + B ≤ n)
    (hp : (1 - s ^ 2) ^ n < p)
    (hgain : (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p ≤ pstar)
    (hpstar : pstar ≤ 1) :
    (A : ℝ) - B < 20 * s * n := by
  have hsnonneg : 0 ≤ s := hs0.le
  have hgpos : 0 < 1 + s := by linarith
  have hqpos : 0 < 1 - s - 2 * s ^ 2 := by nlinarith [sq_nonneg s]
  have hcpos : 0 < 1 - s ^ 2 := by nlinarith [sq_nonneg s]
  have hppos : 0 < p := (pow_pos hcpos n).trans hp
  have hprodpos : 0 < (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p := by positivity
  have hprodle : (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p ≤ 1 :=
    hgain.trans hpstar
  have hlogle := Real.log_le_log hprodpos hprodle
  rw [Real.log_one] at hlogle
  have hlogexpand :
      Real.log ((1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * p) =
        (A : ℝ) * Real.log (1 + s) +
          (B : ℝ) * Real.log (1 - s - 2 * s ^ 2) + Real.log p := by
    rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hgpos.ne')
          (pow_ne_zero _ hqpos.ne')) hppos.ne',
      Real.log_mul (pow_ne_zero _ hgpos.ne') (pow_ne_zero _ hqpos.ne'),
      Real.log_pow, Real.log_pow]
  rw [hlogexpand] at hlogle
  have hlogp := Real.log_lt_log (pow_pos hcpos n) hp
  rw [Real.log_pow] at hlogp
  have hglog := log_one_add_lower hsnonneg
  have hqlog := log_fr_bad_lower hsnonneg hs
  have hclog := log_one_sub_sq_lower hsnonneg hs
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hstepsR : (A : ℝ) + B ≤ n := by exact_mod_cast hsteps
  have hslack : 0 ≤ (n : ℝ) - ((A : ℝ) + B) := sub_nonneg.mpr hstepsR
  by_contra hnot
  push Not at hnot
  have hlower :
      0 < (A : ℝ) * Real.log (1 + s) +
          (B : ℝ) * Real.log (1 - s - 2 * s ^ 2) + Real.log p := by
    have h1 := mul_le_mul_of_nonneg_left hglog hA0
    have h2 := mul_le_mul_of_nonneg_left hqlog hB0
    have h3 := mul_le_mul_of_nonneg_left hclog hn0
    nlinarith [mul_nonneg hsnonneg hslack]
  linarith

lemma exp_neg_le_one_sub_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have habs := Real.abs_exp_sub_one_sub_id_le (x := -x) (by
    rw [abs_neg, abs_of_nonneg hx0]
    linarith)
  have hleft : Real.exp (-x) - 1 + x ≤ |Real.exp (-x) - 1 + x| :=
    le_abs_self _
  have hsquare : x ^ 2 ≤ x / 2 := by nlinarith
  rw [sub_neg_eq_add] at habs
  nlinarith

lemma fr_gain_lower {s : ℝ} {n A B : ℕ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 10) (hsteps : A + B ≤ n) :
    ((1 - s - 2 * s ^ 2) * (1 - s ^ 2)) ^ n ≤
      (1 + s) ^ A * (1 - s - 2 * s ^ 2) ^ B * (1 - s ^ 2) ^ n := by
  let q : ℝ := 1 - s - 2 * s ^ 2
  have hq0 : 0 ≤ q := by dsimp [q]; nlinarith [sq_nonneg s]
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith [sq_nonneg s]
  have hqg : q ≤ 1 + s := by dsimp [q]; nlinarith [sq_nonneg s]
  have hc0 : 0 ≤ 1 - s ^ 2 := by
    have hs_sq : s ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
      simpa [pow_two] using mul_self_le_mul_self hs0 hs
    nlinarith
  have hpowexp : q ^ n ≤ q ^ (A + B) :=
    pow_le_pow_of_le_one hq0 hq1 hsteps
  have hpowbase : q ^ A ≤ (1 + s) ^ A :=
    pow_le_pow_left₀ hq0 hqg A
  calc
    (q * (1 - s ^ 2)) ^ n = q ^ n * (1 - s ^ 2) ^ n := mul_pow _ _ _
    _ ≤ q ^ (A + B) * (1 - s ^ 2) ^ n :=
      mul_le_mul_of_nonneg_right hpowexp (pow_nonneg hc0 n)
    _ = q ^ A * q ^ B * (1 - s ^ 2) ^ n := by rw [pow_add]
    _ ≤ (1 + s) ^ A * q ^ B * (1 - s ^ 2) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc0 n)
      exact mul_le_mul_of_nonneg_right hpowbase (pow_nonneg hq0 B)

lemma fr_constant_exp_gap {eta : ℝ} (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    Real.exp (-(eta ^ 2 / 128)) <
      (1 - eta ^ 3 / 65536 - 2 * (eta ^ 3 / 65536) ^ 2) *
        (1 - (eta ^ 3 / 65536) ^ 2) := by
  let s : ℝ := eta ^ 3 / 65536
  let x : ℝ := eta ^ 2 / 128
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs : s < 1 / 10 := by
    dsimp [s]
    nlinarith [sq_pos_of_pos heta0, mul_pos (sq_pos_of_pos heta0) heta0]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx : x ≤ 1 / 2 := by
    dsimp [x]
    nlinarith [sq_nonneg eta]
  have hsmall : 4 * s < x / 2 := by
    dsimp [s, x]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    nlinarith [mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)]
  have hD : 1 - 4 * s ≤ (1 - s - 2 * s ^ 2) * (1 - s ^ 2) := by
    have hpos : 0 ≤ s * (3 - 3 * s + s ^ 2 + 2 * s ^ 3) := by
      apply mul_nonneg hs0.le
      nlinarith [sq_nonneg s, mul_nonneg (sq_nonneg s) hs0.le]
    nlinarith
  have hexp := exp_neg_le_one_sub_half hx0 hx
  change Real.exp (-x) < (1 - s - 2 * s ^ 2) * (1 - s ^ 2)
  exact hexp.trans_lt (lt_of_lt_of_le (by linarith) hD)

lemma fr_high_endpoint_bound {eta s : ℝ} {n r : ℕ}
    (heta0 : 0 < eta) (h20s : 20 * s < eta / 2) (hn : 0 < n)
    (hrlow : eta * n < r) {F G : Erdos703Iteration.Family n}
    (res : Erdos703Iteration.FRResult s (a := r) (b := r) F G)
    (hbalance : (res.A : ℝ) - res.B < 20 * s * n) (ha0 : res.a' = 0) :
    Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmle : res.m' ≤ n := by have h := res.steps; omega
  have hmleR : (res.m' : ℝ) ≤ n := by exact_mod_cast hmle
  have hbB : res.b' = res.B := by
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    have hu : res.b' + res.d = r := by simpa using res.upper
    omega
  have hrAB : (r : ℝ) ≤ res.A + res.B := by
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    have hd : res.d ≤ res.A := res.shifts
    exact_mod_cast (show r ≤ res.A + res.B by omega)
  have h20sn : 20 * s * n < eta / 2 * n :=
    mul_lt_mul_of_pos_right h20s hnR
  have hBlarge : eta * n / 4 < (res.B : ℝ) := by
    have hrlowR : eta * n < (r : ℝ) := hrlow
    nlinarith
  have hBpos : 0 < res.B := by
    have : (0 : ℝ) < res.B := lt_of_le_of_lt (by positivity) hBlarge
    exact_mod_cast this
  have hmpos : 0 < res.m' := by
    have hb_le := res.interval.2
    rw [hbB] at hb_le
    omega
  have hmR : (0 : ℝ) < res.m' := by exact_mod_cast hmpos
  have hcross : ∀ S ∈ res.F', ∀ T ∈ res.G',
      (res.B : ℝ) ≤ # (S ∩ T) := by
    intro S hS T hT
    rcases res.avoids S hS T hT with hlt | hgt
    · omega
    · rw [hbB] at hgt
      exact_mod_cast hgt.le
  have hhigh := Erdos703Endpoints.cross_high hmpos
    (Erdos703Endpoints.fairCubeMcDiarmid res.m') res.F' res.G'
    (res.B : ℝ) (by positivity) hcross
  have hBbase0 : 0 ≤ eta * n / 4 := by positivity
  have hBsq := mul_self_lt_mul_self hBbase0 hBlarge
  have hdiv : (eta ^ 2 / 128) * n ≤ (res.B : ℝ) ^ 2 / res.m' := by
    apply (le_div_iff₀ hmR).2
    have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta0
    have hmnonneg : (0 : ℝ) ≤ res.m' := hmR.le
    have hprodle :=
      mul_le_mul_of_nonneg_left hmleR (mul_nonneg heta2.le hnR.le)
    nlinarith [sq_nonneg (res.B : ℝ)]
  have hexp : Real.exp (-(res.B : ℝ) ^ 2 / res.m') ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
    apply Real.exp_le_exp.mpr
    simpa [neg_div] using neg_le_neg hdiv
  exact hhigh.trans hexp

lemma fr_low_endpoint_bound {eta s : ℝ} {n r : ℕ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) (h10s : 10 * s < eta / 2)
    (hn : 0 < n) (hrhigh : (r : ℝ) < (1 / 2 - eta) * n)
    (habsorb : Real.log 4 < eta ^ 2 * n / 128)
    {F G : Erdos703Iteration.Family n}
    (res : Erdos703Iteration.FRResult s (a := r) (b := r) F G)
    (hbalance : (res.A : ℝ) - res.B < 20 * s * n) (hbm : res.b' = res.m') :
    Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
      Real.exp (-((eta ^ 2 / 128) * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hba : res.b' = res.a' + res.B := by
    have hu : res.b' + res.d = r := by simpa using res.upper
    have hl : res.a' + res.B + res.d = r := by simpa using res.lower
    omega
  have hmAB : res.m' = res.a' + res.B := by omega
  have hnr : (1 / 2 + eta) * n < (n : ℝ) - r := by nlinarith
  have hnrAB : (n : ℝ) - r = (res.A : ℝ) + res.B - res.d := by
    have hsR : (res.m' : ℝ) + res.A + res.B = n := by
      exact_mod_cast res.steps
    have hu : res.b' + res.d = r := by simpa using res.upper
    rw [hbm] at hu
    have huR : (res.m' : ℝ) + res.d = r := by exact_mod_cast hu
    linarith
  have hBlarge : (1 / 4 + eta / 2 - 10 * s) * n < (res.B : ℝ) := by
    rw [hnrAB] at hnr
    have hd0 : (0 : ℝ) ≤ res.d := by positivity
    nlinarith
  have hcoef : (1 / 4 : ℝ) < 1 / 4 + eta / 2 - 10 * s := by linarith
  have hmul : (1 / 4 : ℝ) * n <
      (1 / 4 + eta / 2 - 10 * s) * n :=
    mul_lt_mul_of_pos_right hcoef hnR
  have hmul' : (n : ℝ) / 4 <
      (1 / 4 + eta / 2 - 10 * s) * n := by
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have hBn4 : (n : ℝ) / 4 < res.B := hmul'.trans hBlarge
  have hBm : (1 / 2 + eta / 2) * res.m' < (res.B : ℝ) := by
    have hmr : (res.m' : ℝ) < (1 / 2 - eta) * n := by
      have hmd : res.m' ≤ r := by
        have hu : res.b' + res.d = r := by simpa using res.upper
        rw [hbm] at hu
        omega
      have hmdR : (res.m' : ℝ) ≤ r := by exact_mod_cast hmd
      exact hmdR.trans_lt hrhigh
    have hcoefpos : 0 < 1 / 2 + eta / 2 := by linarith
    have hprod := mul_lt_mul_of_pos_left hmr hcoefpos
    have hcoefMargin :
        (1 / 2 + eta / 2) * (1 / 2 - eta) ≤
          1 / 4 + eta / 2 - 10 * s := by
      have hpositive : 0 < 3 * eta / 4 + eta ^ 2 / 2 - 10 * s := by
        nlinarith [sq_nonneg eta]
      nlinarith
    have hmargin :
        (1 / 2 + eta / 2) * ((1 / 2 - eta) * n) ≤
          (1 / 4 + eta / 2 - 10 * s) * n := by
      calc
        (1 / 2 + eta / 2) * ((1 / 2 - eta) * n) =
            ((1 / 2 + eta / 2) * (1 / 2 - eta)) * n := by ring
        _ ≤ (1 / 4 + eta / 2 - 10 * s) * n :=
          mul_le_mul_of_nonneg_right hcoefMargin hnR.le
    exact (hprod.trans_le hmargin).trans hBlarge
  have hmpos : 0 < res.m' := by
    have hnquarter0 : (0 : ℝ) ≤ n / 4 := by positivity
    have hBposR : (0 : ℝ) < res.B := hnquarter0.trans_lt hBn4
    have hBpos : 0 < res.B := by exact_mod_cast hBposR
    have hBmle : res.B ≤ res.m' := by rw [hmAB]; omega
    exact hBpos.trans_le hBmle
  have hcross : ∀ S ∈ res.F', ∀ T ∈ res.G',
      (#(S ∩ T) : ℝ) < (1 / 2 - eta / 2) * res.m' := by
    intro S hS T hT
    have hcardm : #(S ∩ T) ≤ res.m' := by
      calc
        #(S ∩ T) ≤ #S := card_le_card inter_subset_left
        _ ≤ #(Finset.univ : Finset (Fin res.m')) := card_le_univ _
        _ = res.m' := by simp
    have hcarda : #(S ∩ T) < res.a' := by
      rcases res.avoids S hS T hT with hlt | hgt
      · exact hlt
      · omega
    have hcast : (#(S ∩ T) : ℝ) < res.a' := by exact_mod_cast hcarda
    have hmaR : (res.m' : ℝ) = res.a' + res.B := by exact_mod_cast hmAB
    nlinarith
  have hlow := Erdos703Endpoints.cross_low hmpos
    (Erdos703Endpoints.fairCubeMcDiarmid res.m')
    (Erdos703Endpoints.cubeMean_card res.m') res.F' res.G'
    (eta / 2) (by positivity) hcross
  have hterm1 :
      2 * Real.exp (-((eta / 2) ^ 2 * res.m') / 2) ≤
        4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) := by
    have he : Real.exp (-((eta / 2) ^ 2 * res.m') / 2) ≤
        Real.exp (-((eta / 2) ^ 2 * res.m') / 4) := by
      apply Real.exp_le_exp.mpr
      have : 0 ≤ (eta / 2) ^ 2 * (res.m' : ℝ) := by positivity
      linarith
    nlinarith [Real.exp_pos (-((eta / 2) ^ 2 * res.m') / 4)]
  have hmax :
      max (2 * Real.exp (-((eta / 2) ^ 2 * res.m') / 2))
          (4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4)) ≤
        4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) :=
    max_le hterm1 (le_refl _)
  have habs :
      4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) ≤
        Real.exp (-((eta ^ 2 / 128) * n)) := by
    have hfour : 4 * Real.exp (-((eta / 2) ^ 2 * res.m') / 4) =
        Real.exp (Real.log 4 + -((eta / 2) ^ 2 * res.m') / 4) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    rw [hfour]
    apply Real.exp_le_exp.mpr
    have hBmle : res.B ≤ res.m' := by rw [hmAB]; omega
    have hBmleR : (res.B : ℝ) ≤ res.m' := by exact_mod_cast hBmle
    have hmquarter : (n : ℝ) / 4 < res.m' := hBn4.trans_le hBmleR
    have hscalePos : 0 < eta ^ 2 / 16 := by positivity
    have hscaled := mul_lt_mul_of_pos_left hmquarter hscalePos
    nlinarith
  exact (hlow.trans hmax).trans habs

/-- Quantitative cross-family forbidden-intersection theorem in sufficiently
large dimension.  This is the Frankl--Rödl theorem in the exact form used for
Erdős Problem 703. -/
theorem cross_forbidden_intersection_large {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ N : ℕ, ∀ {n r : ℕ}, N ≤ n →
      eta * n < r → r < (1 / 2 - eta) * n →
      ∀ F G : Erdos703Iteration.Family n,
        Erdos703Iteration.CrossAvoids r r F G →
        Erdos703Iteration.density F * Erdos703Iteration.density G ≤
          (1 - (eta ^ 3 / 65536) ^ 2) ^ n := by
  let s : ℝ := eta ^ 3 / 65536
  let q : ℝ := 1 - s - 2 * s ^ 2
  let c : ℝ := 1 - s ^ 2
  let x : ℝ := eta ^ 2 / 128
  have hs0 : 0 < s := by dsimp [s]; positivity
  have hs : s ≤ 1 / 10 := by
    dsimp [s]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hmul := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
    nlinarith [sq_nonneg eta]
  have hq0 : 0 < q := by dsimp [q]; nlinarith [sq_nonneg s]
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith [sq_nonneg s]
  have hc0 : 0 < c := by dsimp [c]; nlinarith [sq_nonneg s]
  have h20s : 20 * s < eta / 2 := by
    dsimp [s]
    have heta0' : 0 < eta ^ 2 := sq_pos_of_pos heta0
    have hetaBound : eta < 819 := heta.trans (by norm_num)
    nlinarith [mul_pos heta0' (sub_pos.mpr hetaBound)]
  have h10s : 10 * s < eta / 2 := lt_trans (by linarith) h20s
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (128 * Real.log 4 / eta ^ 2)
  refine ⟨max N₀ 1, ?_⟩
  intro n r hnN hrlow hrhigh F G havoid
  have hnN₀ : N₀ ≤ n := (le_max_left _ _).trans hnN
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < max N₀ 1) hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrnR : (r : ℝ) < n := hrhigh.trans_le (by
    have : 1 / 2 - eta ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right this hnR.le)
  have hrn : r ≤ n := by exact_mod_cast hrnR.le
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta0
  have hNmul : 128 * Real.log 4 < (N₀ : ℝ) * eta ^ 2 := by
    exact (div_lt_iff₀ heta2).mp hN₀
  have hnN₀R : (N₀ : ℝ) ≤ n := by exact_mod_cast hnN₀
  have habsorb : Real.log 4 < eta ^ 2 * n / 128 := by
    nlinarith [mul_le_mul_of_nonneg_right hnN₀R heta2.le]
  by_contra hnot
  push Not at hnot
  have hp : c ^ n < Erdos703Iteration.density F * Erdos703Iteration.density G := by
    simpa [c, s] using hnot
  let res := Erdos703Iteration.fr_iterate hs0.le hs F G (le_refl r)
    hrn
    havoid
  have hsteps : res.A + res.B ≤ n := by
    have h := res.steps
    omega
  have hpstar :
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤ 1 := by
    calc
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
          1 * 1 := mul_le_mul (Erdos703Iteration.density_le_one _)
            (Erdos703Iteration.density_le_one _)
            (Erdos703Iteration.density_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hbalance : (res.A : ℝ) - res.B < 20 * s * n :=
    good_bad_balance hs0 hs hsteps hp (by simpa [mul_assoc] using res.density_gain) hpstar
  have hmle : res.m' ≤ n := by
    have h := res.steps
    omega
  have hmleR : (res.m' : ℝ) ≤ n := by exact_mod_cast hmle
  have hterminal :
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' ≤
        Real.exp (-(x * n)) := by
    rcases res.terminal with ha0 | hbm
    · simpa [x] using
        fr_high_endpoint_bound heta0 h20s hn hrlow res hbalance ha0
    · simpa [x] using
        fr_low_endpoint_bound heta0 heta h10s hn hrhigh habsorb res hbalance hbm
  have hDgain : (q * c) ^ n <
      Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' := by
    have hbase := fr_gain_lower hs0.le hs hsteps
    change (q * c) ^ n ≤
        (1 + s) ^ res.A * q ^ res.B * c ^ n at hbase
    have hcoefpos : 0 < (1 + s) ^ res.A * q ^ res.B := by positivity
    have hmiddle :
        (1 + s) ^ res.A * q ^ res.B * c ^ n <
          (1 + s) ^ res.A * q ^ res.B *
            (Erdos703Iteration.density F * Erdos703Iteration.density G) :=
      mul_lt_mul_of_pos_left hp hcoefpos
    have hgain :
        (1 + s) ^ res.A * q ^ res.B *
            (Erdos703Iteration.density F * Erdos703Iteration.density G) ≤
          Erdos703Iteration.density res.F' * Erdos703Iteration.density res.G' := by
      simpa [q, mul_assoc] using res.density_gain
    exact hbase.trans_lt (hmiddle.trans_le hgain)
  have hgap : Real.exp (-x) < q * c := by
    simpa [x, q, c, s] using fr_constant_exp_gap heta0 heta
  have hpows : Real.exp (-x) ^ n < (q * c) ^ n :=
    pow_lt_pow_left₀ hgap (Real.exp_nonneg _) hn.ne'
  have hexppow : Real.exp (-x) ^ n = Real.exp (-(x * n)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexppow] at hpows
  linarith

/-- The one-family density consequence, with an explicit base strictly below
one. -/
theorem forbidden_family_density_large {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ N : ℕ, ∀ {n r : ℕ}, N ≤ n →
      eta * n < r → r < (1 / 2 - eta) * n →
      ∀ F : Erdos703Iteration.Family n,
        Erdos703Iteration.CrossAvoids r r F F →
        Erdos703Iteration.density F <
          (1 - (eta ^ 3 / 65536) ^ 2 / 4) ^ n := by
  obtain ⟨N, hN⟩ := cross_forbidden_intersection_large heta0 heta
  refine ⟨max N 1, ?_⟩
  intro n r hnN hrlow hrhigh F havoid
  have hnN' : N ≤ n := (le_max_left _ _).trans hnN
  have hn : 0 < n := lt_of_lt_of_le (by omega : 0 < max N 1) hnN
  have hcross := hN hnN' hrlow hrhigh F F havoid
  let u : ℝ := (eta ^ 3 / 65536) ^ 2
  let b : ℝ := 1 - u / 4
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hsmall : eta ^ 3 / 65536 < 1 := by
      have := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
      nlinarith [sq_nonneg eta]
    have hsq := mul_self_lt_mul_self
      (by positivity : 0 ≤ eta ^ 3 / 65536) hsmall
    simpa [pow_two] using hsq
  have hb0 : 0 < b := by dsimp [b]; nlinarith
  have hcb : 1 - u < b ^ 2 := by
    dsimp [b]
    nlinarith [sq_pos_of_pos hu0]
  have hcpow : (1 - u) ^ n < (b ^ 2) ^ n :=
    pow_lt_pow_left₀ hcb (by linarith : 0 ≤ 1 - u) hn.ne'
  by_contra hnot
  push Not at hnot
  have hsq : b ^ n * b ^ n ≤
      Erdos703Iteration.density F * Erdos703Iteration.density F :=
    mul_le_mul hnot hnot (pow_nonneg hb0.le n)
      (Erdos703Iteration.density_nonneg F)
  have hid : b ^ n * b ^ n = (b ^ 2) ^ n := by
    rw [pow_two, mul_pow]
  rw [hid] at hsq
  change Erdos703Iteration.density F * Erdos703Iteration.density F ≤
    (1 - u) ^ n at hcross
  linarith

lemma density_lt_base_pow_of_card_lt {N n : ℕ} (hN : 1 ≤ N)
    (hnN : n < N) {F : Erdos703Iteration.Family n}
    (hproper : #F < 2 ^ n) :
    Erdos703Iteration.density F <
      (1 - 1 / (2 : ℝ) ^ (2 * N)) ^ n := by
  let u : ℝ := 1 / (2 : ℝ) ^ (2 * N)
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 * N))).2 (by
      have hp : (1 : ℝ) < (2 : ℝ) ^ (2 * N) :=
        one_lt_pow₀ (by norm_num) (by omega)
      exact hp.le)
  have hBernoulli : 1 - (n : ℝ) * u ≤ (1 - u) ^ n := by
    have h := one_add_mul_le_pow (a := -u) (by linarith) n
    simpa [sub_eq_add_neg, mul_neg] using h
  have hnatpow : n * 2 ^ n < 2 ^ (2 * N) := by
    have hn2N : n < 2 ^ N := hnN.trans_le (Nat.le_of_lt N.lt_two_pow_self)
    have hpow : 2 ^ n ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hnN.le
    calc
      n * 2 ^ n < 2 ^ N * 2 ^ n := Nat.mul_lt_mul_of_pos_right hn2N (pow_pos (by omega) _)
      _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul_left _ hpow
      _ = 2 ^ (2 * N) := by rw [← pow_add]; congr 1; omega
  have hnu : (n : ℝ) * u < 1 / (2 : ℝ) ^ n := by
    dsimp [u]
    rw [mul_one_div]
    have hcast : (n : ℝ) * (2 : ℝ) ^ n < (2 : ℝ) ^ (2 * N) := by
      exact_mod_cast hnatpow
    exact (div_lt_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hcast)
  have hcard : (#F : ℝ) ≤ (2 : ℝ) ^ n - 1 := by
    have hnat : #F + 1 ≤ 2 ^ n := by omega
    have hcast : (#F : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
    linarith
  change (#F : ℝ) / (2 : ℝ) ^ n < (1 - u) ^ n
  have hdensity : (#F : ℝ) / (2 : ℝ) ^ n ≤
      1 - 1 / (2 : ℝ) ^ n := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).2
    field_simp
    linarith
  have hgap : 1 - 1 / (2 : ℝ) ^ n < 1 - (n : ℝ) * u := by linarith
  exact hdensity.trans_lt (hgap.trans_le hBernoulli)

lemma card_lt_cube_of_cross_avoids {n r : ℕ} (hrn : r ≤ n)
    {F : Erdos703Iteration.Family n}
    (havoid : Erdos703Iteration.CrossAvoids r r F F) : #F < 2 ^ n := by
  have hsub : F ⊆ (Finset.univ : Finset (Fin n)).powerset := by simp
  have hproper : F ⊂ (Finset.univ : Finset (Fin n)).powerset := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    have hnonempty : ((Finset.univ : Finset (Fin n)).powersetCard r).Nonempty := by
      apply card_pos.mp
      rw [card_powersetCard]
      simpa using Nat.choose_pos hrn
    obtain ⟨S, hS⟩ := hnonempty
    have hSdata := mem_powersetCard.mp hS
    have hSF : S ∈ F := by rw [heq]; exact mem_powerset.mpr hSdata.1
    rcases havoid S hSF S hSF with hlt | hgt <;>
      have hself : #(S ∩ S) = r := by simpa using hSdata.2
    · omega
    · omega
  simpa using card_lt_card hproper

/-- Uniform all-dimensions form of the one-family theorem. -/
theorem forbidden_family_density {eta : ℝ}
    (heta0 : 0 < eta) (heta : eta < 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∀ {n r : ℕ}, eta * n < r → r < (1 / 2 - eta) * n →
        ∀ F : Erdos703Iteration.Family n,
          Erdos703Iteration.CrossAvoids r r F F →
          Erdos703Iteration.density F < b ^ n := by
  obtain ⟨N, hlarge⟩ := forbidden_family_density_large heta0 heta
  let M : ℕ := max N 1
  have hM : 1 ≤ M := by dsimp [M]; exact le_max_right _ _
  let u : ℝ := (eta ^ 3 / 65536) ^ 2
  let bLarge : ℝ := 1 - u / 4
  let bSmall : ℝ := 1 - 1 / (2 : ℝ) ^ (2 * M)
  let b : ℝ := max bLarge bSmall
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have heta64 : eta < 64 := heta.trans (by norm_num)
    have hsmall : eta ^ 3 / 65536 < 1 := by
      have := mul_pos (sq_pos_of_pos heta0) (sub_pos.mpr heta64)
      nlinarith [sq_nonneg eta]
    have hsq := mul_self_lt_mul_self
      (by positivity : 0 ≤ eta ^ 3 / 65536) hsmall
    simpa [pow_two] using hsq
  have hbLarge0 : 0 < bLarge := by dsimp [bLarge]; nlinarith
  have hbLarge1 : bLarge < 1 := by dsimp [bLarge]; linarith
  have hbSmall0 : 0 < bSmall := by
    dsimp [bSmall]
    have hp : (1 : ℝ) < (2 : ℝ) ^ (2 * M) := by
      have : 0 < 2 * M := by omega
      exact one_lt_pow₀ (by norm_num) this.ne'
    have hfrac : (1 : ℝ) / (2 : ℝ) ^ (2 * M) < 1 :=
      (div_lt_one (by positivity)).2 hp
    linarith
  have hbSmall1 : bSmall < 1 := by
    dsimp [bSmall]
    have hpos : 0 < 1 / (2 : ℝ) ^ (2 * M) := by positivity
    linarith
  refine ⟨b, lt_of_lt_of_le hbLarge0 (le_max_left _ _),
    max_lt hbLarge1 hbSmall1, ?_⟩
  intro n r hrlow hrhigh F havoid
  have hn : 0 < n := by
    by_contra hh
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hh
    subst n
    norm_num at hrhigh
    have hr0 : (0 : ℝ) ≤ r := by positivity
    linarith
  by_cases hnM : M ≤ n
  · have hnN : N ≤ n := (le_max_left _ _).trans hnM
    have h := hlarge hnN hrlow hrhigh F havoid
    change Erdos703Iteration.density F < bLarge ^ n at h
    exact h.trans_le (pow_le_pow_left₀ hbLarge0.le (le_max_left _ _) n)
  · have hnM' : n < M := Nat.lt_of_not_ge hnM
    have hrnR : (r : ℝ) < n := hrhigh.trans_le (by
      have hc : 1 / 2 - eta ≤ 1 := by linarith
      simpa using mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ n))
    have hrn : r ≤ n := by exact_mod_cast hrnR.le
    have hproper := card_lt_cube_of_cross_avoids hrn havoid
    have h := density_lt_base_pow_of_card_lt hM hnM' hproper
    change Erdos703Iteration.density F < bSmall ^ n at h
    exact h.trans_le (pow_le_pow_left₀ hbSmall0.le (le_max_right _ _) n)

end

end Erdos703FranklRodl

/-! ### Upstream module `JSP573/External/Erdos703.lean` -/

section
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 703.
https://www.erdosproblems.com/forum/thread/703

Informal authors:
- Péter Frankl
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos703.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Erdős Problem 703: forbidden intersections

For `n r : ℕ`, `T n r` is the largest size of a family of subsets of
`{0, ..., n - 1}` such that no two members (including a member paired with
itself) have intersection of size `r`.

The main theorem `erdos_703_gap` is the Frankl--Rödl exponential gap: if `r` stays
a positive linear distance from both `0` and `n / 2`, then `T n r` is bounded
by `(2 - δ) ^ n`, where `δ > 0` depends only on that distance.

The mathematical proof and the formalization map are in `tex/703.tex`.
-/

open _root_.Nat _root_.Finset _root_.Real
noncomputable section

attribute [local instance] Classical.propDecidable

/-- No two members of `𝓕`, including a member paired with itself, meet in `r` points. -/
def AvoidsRIntersection (r : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, #(A ∩ B) ≠ r

/-- The extremal quantity in Erdős Problem 703. -/
def T (n r : ℕ) : ℕ :=
  (((range n).powerset.powerset).filter (AvoidsRIntersection r)).sup card

lemma mem_admissibleFamilies_iff {n r : ℕ} {𝓕 : Finset (Finset ℕ)} :
    𝓕 ∈ ((range n).powerset.powerset).filter (AvoidsRIntersection r) ↔
      𝓕 ⊆ (range n).powerset ∧ AvoidsRIntersection r 𝓕 := by
  simp only [mem_filter, mem_powerset]

lemma card_le_T {n r : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hsub : 𝓕 ⊆ (range n).powerset) (havoid : AvoidsRIntersection r 𝓕) :
    #𝓕 ≤ T n r := by
  exact le_sup (s := ((range n).powerset.powerset).filter (AvoidsRIntersection r))
    (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hsub, havoid⟩)

lemma T_le_of_forall {n r M : ℕ}
    (h : ∀ 𝓕 : Finset (Finset ℕ), 𝓕 ⊆ (range n).powerset →
      AvoidsRIntersection r 𝓕 → #𝓕 ≤ M) :
    T n r ≤ M := by
  apply Finset.sup_le
  intro 𝓕 h𝓕
  rw [mem_filter, mem_powerset] at h𝓕
  exact h 𝓕 h𝓕.1 h𝓕.2

/-! ## The exact elementary case `r = 0` -/

lemma card_le_of_avoids_zero (n : ℕ) (hn : 1 ≤ n) (𝓕 : Finset (Finset ℕ))
    (hsub : 𝓕 ⊆ (range n).powerset) (havoid : AvoidsRIntersection 0 𝓕) :
    #𝓕 ≤ 2 ^ (n - 1) := by
  let c : Finset ℕ → Finset ℕ := fun A ↦ range n \ A
  have hc_mem : ∀ A ∈ 𝓕, c A ∈ (range n).powerset := by
    intro A hA
    exact mem_powerset.mpr sdiff_subset
  have hc_invol : ∀ A ∈ 𝓕, c (c A) = A := by
    intro A hA
    exact Finset.sdiff_sdiff_eq_self (mem_powerset.mp (hsub hA))
  have hc_notMem : ∀ A ∈ 𝓕, c A ∉ 𝓕 := by
    intro A hA hcA
    have hne := havoid A hA (c A) hcA
    exact hne (by simp [c])
  have hdisj : Disjoint 𝓕 (𝓕.image c) := by
    rw [disjoint_left]
    intro A hA hAc
    rw [mem_image] at hAc
    obtain ⟨B, hB, rfl⟩ := hAc
    exact hc_notMem B hB hA
  have hinj : Set.InjOn c 𝓕 := by
    intro A hA B hB hAB
    have := congrArg c hAB
    simpa [hc_invol A hA, hc_invol B hB] using this
  have hunion : 𝓕 ∪ 𝓕.image c ⊆ (range n).powerset := by
    refine union_subset hsub ?_
    intro A hA
    rw [mem_image] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    exact hc_mem B hB
  have htwo : #𝓕 + #𝓕 ≤ 2 ^ n := by
    calc
      #𝓕 + #𝓕 = #(𝓕 ∪ 𝓕.image c) := by
        rw [card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]
      _ ≤ #(range n).powerset := card_le_card hunion
      _ = 2 ^ n := by simp
  have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.pow_succ']
  omega

/-- The star consisting of all subsets through `0`. -/
def starFamily (n : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦ 0 ∈ A

lemma starFamily_card (n : ℕ) (hn : 1 ≤ n) : #(starFamily n) = 2 ^ (n - 1) := by
  have h0 : 0 ∈ range n := mem_range.mpr hn
  have hcard : #((range n).erase 0) = n - 1 := by simp [h0]
  rw [← hcard, ← card_powerset]
  apply card_nbij' (fun A ↦ A.erase 0) (fun B ↦ insert 0 B)
  · intro A hA
    rw [mem_coe, starFamily, mem_filter, mem_powerset] at hA
    rw [mem_coe, mem_powerset]
    intro x hx
    rw [mem_erase] at hx ⊢
    exact ⟨hx.1, hA.1 hx.2⟩
  · intro B hB
    rw [mem_coe, mem_powerset] at hB
    rw [mem_coe, starFamily, mem_filter, mem_powerset]
    refine ⟨?_, mem_insert_self 0 B⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact h0
    · exact (mem_erase.mp (hB hx)).2
  · intro A hA
    rw [mem_coe, starFamily, mem_filter] at hA
    exact insert_erase hA.2
  · intro B hB
    rw [mem_coe, mem_powerset] at hB
    have h0B : 0 ∉ B := fun h ↦ (mem_erase.mp (hB h)).1 rfl
    exact erase_insert h0B

lemma starFamily_avoids_zero (n : ℕ) : AvoidsRIntersection 0 (starFamily n) := by
  intro A hA B hB
  rw [starFamily, mem_filter] at hA hB
  have h0 : 0 ∈ A ∩ B := mem_inter.mpr ⟨hA.2, hB.2⟩
  exact ne_of_gt (card_pos.mpr ⟨0, h0⟩)

/-- The trivial exact value `T(n,0) = 2^(n-1)`. -/
theorem T_zero (n : ℕ) (hn : 1 ≤ n) : T n 0 = 2 ^ (n - 1) := by
  apply le_antisymm
  · exact T_le_of_forall fun 𝓕 hsub havoid ↦ card_le_of_avoids_zero n hn 𝓕 hsub havoid
  · rw [← starFamily_card n hn]
    exact card_le_T (filter_subset _ _) (starFamily_avoids_zero n)

/-! ## The Frankl--Füredi constructions -/

/-- The fixed-`r` construction when `n + r` is odd. -/
def franklFurediOdd (n r : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦ (n + r) / 2 < #A ∨ #A < r

lemma franklFurediOdd_avoids (n r : ℕ) :
    AvoidsRIntersection r (franklFurediOdd n r) := by
  intro A hA B hB
  rw [franklFurediOdd, mem_filter, mem_powerset] at hA hB
  have hunion : #(A ∪ B) ≤ n := by
    calc
      #(A ∪ B) ≤ #(range n) := card_le_card (union_subset hA.1 hB.1)
      _ = n := card_range n
  have hie := card_union_add_card_inter A B
  have hiA : #(A ∩ B) ≤ #A := card_le_card inter_subset_left
  have hiB : #(A ∩ B) ≤ #B := card_le_card inter_subset_right
  rcases hA.2 with hAl | hAs <;> rcases hB.2 with hBl | hBs <;> omega

lemma franklFurediOdd_card_le_T (n r : ℕ) : #(franklFurediOdd n r) ≤ T n r :=
  card_le_T (filter_subset _ _) (franklFurediOdd_avoids n r)

/-- The fixed-`r` construction when `n + r` is even. -/
def franklFurediEven (n r : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun A ↦
    (n + r) / 2 ≤ #(A.filter (· ≠ 0)) ∨ #A < r

lemma franklFurediEven_avoids (n r : ℕ) (hn : 1 ≤ n) (heven : (n + r) % 2 = 0) :
    AvoidsRIntersection r (franklFurediEven n r) := by
  intro A hA B hB
  rw [franklFurediEven, mem_filter, mem_powerset] at hA hB
  let A₀ := A.filter (· ≠ 0)
  let B₀ := B.filter (· ≠ 0)
  have hA₀A : A₀ ⊆ A := filter_subset _ _
  have hB₀B : B₀ ⊆ B := filter_subset _ _
  have hint : #(A₀ ∩ B₀) ≤ #(A ∩ B) :=
    card_le_card (inter_subset_inter hA₀A hB₀B)
  have hground : #((range n).filter (· ≠ 0)) = n - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_range.mpr hn), card_range]
  have hA₀sub : A₀ ⊆ (range n).filter (· ≠ 0) :=
    filter_subset_filter (· ≠ 0) hA.1
  have hB₀sub : B₀ ⊆ (range n).filter (· ≠ 0) :=
    filter_subset_filter (· ≠ 0) hB.1
  have hunion : #(A₀ ∪ B₀) ≤ n - 1 := by
    calc
      #(A₀ ∪ B₀) ≤ #((range n).filter (· ≠ 0)) :=
        card_le_card (union_subset hA₀sub hB₀sub)
      _ = n - 1 := hground
  have hie := card_union_add_card_inter A₀ B₀
  have hhalf : 2 * ((n + r) / 2) = n + r := by omega
  have hiA : #(A ∩ B) ≤ #A := card_le_card inter_subset_left
  have hiB : #(A ∩ B) ≤ #B := card_le_card inter_subset_right
  rcases hA.2 with hAl | hAs
  · rcases hB.2 with hBl | hBs
    · intro heq
      change (n + r) / 2 ≤ #A₀ at hAl
      change (n + r) / 2 ≤ #B₀ at hBl
      have hinter : r + 1 ≤ #(A₀ ∩ B₀) := by omega
      omega
    · omega
  · omega

lemma franklFurediEven_card_le_T (n r : ℕ) (hn : 1 ≤ n) (heven : (n + r) % 2 = 0) :
    #(franklFurediEven n r) ≤ T n r :=
  card_le_T (filter_subset _ _) (franklFurediEven_avoids n r hn heven)

/-! ## Passing between subsets of range n and subsets of Fin n -/

def toFinSet (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ (i : ℕ) ∈ A

@[simp] lemma mem_toFinSet {n : ℕ} {A : Finset ℕ} {i : Fin n} :
    i ∈ toFinSet n A ↔ (i : ℕ) ∈ A := by simp [toFinSet]

lemma toFinSet_inter (n : ℕ) (A B : Finset ℕ) :
    toFinSet n (A ∩ B) = toFinSet n A ∩ toFinSet n B := by
  ext i
  simp

lemma card_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ range n) :
    #(toFinSet n A) = #A := by
  refine Finset.card_bij (s := toFinSet n A) (t := A)
    (fun i _ ↦ (i : ℕ)) ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro x hx
    have hxn : x < n := mem_range.mp (hA hx)
    let i : Fin n := ⟨x, hxn⟩
    exact ⟨i, by simp [i, hx], rfl⟩

lemma toFinSet_injOn {n : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ range n) (hB : B ⊆ range n)
    (h : toFinSet n A = toFinSet n B) : A = B := by
  ext x
  by_cases hxn : x < n
  · let i : Fin n := ⟨x, hxn⟩
    have hi := Finset.ext_iff.mp h i
    simpa [i] using hi
  · have hxA : x ∉ A := fun hx ↦ hxn (mem_range.mp (hA hx))
    have hxB : x ∉ B := fun hx ↦ hxn (mem_range.mp (hB hx))
    simp [hxA, hxB]

def toFinFamily (n : ℕ) (fam : Finset (Finset ℕ)) :
    Erdos703Iteration.Family n := fam.image (toFinSet n)

lemma card_toFinFamily {n : ℕ} {fam : Finset (Finset ℕ)}
    (hsub : fam ⊆ (range n).powerset) : #(toFinFamily n fam) = #fam := by
  unfold toFinFamily
  apply Finset.card_image_of_injOn
  intro A hA B hB hAB
  exact toFinSet_injOn (mem_powerset.mp (hsub hA)) (mem_powerset.mp (hsub hB)) hAB

lemma toFinFamily_crossAvoids {n r : ℕ} {fam : Finset (Finset ℕ)}
    (hsub : fam ⊆ (range n).powerset) (havoid : AvoidsRIntersection r fam) :
    Erdos703Iteration.CrossAvoids r r (toFinFamily n fam) (toFinFamily n fam) := by
  intro S hS T hT
  rw [toFinFamily, mem_image] at hS hT
  obtain ⟨A, hA, rfl⟩ := hS
  obtain ⟨B, hB, rfl⟩ := hT
  have hAB : A ∩ B ⊆ range n :=
    inter_subset_left.trans (mem_powerset.mp (hsub hA))
  have hne : #(toFinSet n A ∩ toFinSet n B) ≠ r := by
    intro heq
    apply havoid A hA B hB
    rw [← card_toFinSet hAB, toFinSet_inter]
    exact heq
  exact Nat.lt_or_gt_of_ne hne

/-! ## The Frankl--Rödl resolution -/

/-- Erdős Problem 703: forbidden intersections in the linear range have a
uniform exponential gap below the size of the Boolean cube. -/
theorem erdos_703_gap :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n →
        (T n r : ℝ) < (2 - δ) ^ n := by
  intro ε hε
  by_cases hεhalf : ε < 1 / 2
  · obtain ⟨b, hb0, hb1, hfamily⟩ :=
      Erdos703FranklRodl.forbidden_family_density hε hεhalf
    refine ⟨2 - 2 * b, by linarith, ?_⟩
    intro n r hrlow hrhigh
    let admissible := ((range n).powerset.powerset).filter (AvoidsRIntersection r)
    have hadmissible : admissible.Nonempty := by
      refine ⟨∅, ?_⟩
      simp [admissible, AvoidsRIntersection]
    obtain ⟨fam, hfammem, hfammax⟩ :=
      Finset.exists_mem_eq_sup admissible hadmissible card
    have hfamdata : fam ⊆ (range n).powerset ∧ AvoidsRIntersection r fam := by
      simpa [admissible, mem_admissibleFamilies_iff] using hfammem
    have hden := hfamily hrlow hrhigh (toFinFamily n fam)
      (toFinFamily_crossAvoids hfamdata.1 hfamdata.2)
    have hcard := card_toFinFamily hfamdata.1
    change (#(toFinFamily n fam) : ℝ) / (2 : ℝ) ^ n < b ^ n at hden
    rw [hcard] at hden
    have hcardBound : (#fam : ℝ) < (2 * b) ^ n := by
      have hmul :=
        (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp hden
      rw [mul_comm, ← mul_pow] at hmul
      exact hmul
    have hTeq : T n r = #fam := by
      simpa [T, admissible] using hfammax
    rw [hTeq]
    convert hcardBound using 1; ring
  · refine ⟨1, by norm_num, ?_⟩
    intro n r hrlow hrhigh
    have hcoef : 1 / 2 - ε ≤ 0 := by linarith
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hright : (1 / 2 - ε) * n ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef hn0
    have hr0 : (0 : ℝ) ≤ r := by positivity
    exfalso
    linarith

end

end

/-! ### Upstream module `JSP573/FF/Basic.lean` -/

section
/-!
# Frankl–Füredi 1984: basic definitions and the disjointness count

Setting (Frankl–Füredi, *On hypergraphs without two edges intersecting in a given number of
vertices*, JCTA 36 (1984) 230–236): `X = range n`, `t ≥ 1`, and a family `𝓕` of subsets of `X`
with `#(A ∩ B) ≠ t` for all `A, B ∈ 𝓕` (`Erdos703.AvoidsRIntersection t 𝓕`, which also excludes
members of size `t` because `A = B` is allowed).

* `level 𝓕 i` — members of size `i` (`𝓕_i` in the paper), `f_i = #(level 𝓕 i)`.
* `shadow g 𝓕` — all `g`-element subsets of members (`∂_g 𝓕`).
* `complFamily n 𝓕` — complements `range n \ A` of members.
* `inclVec n g A` — the row of the containment matrix `M(𝓕, g)` belonging to `A`.
* `lcmUpTo t = lcm (1, …, t)` and `qBound t = t + 1 + lcmUpTo t` (the paper's `q(t)`).
-/

open _root_.Finset

namespace FranklFuredi

/-- The members of `𝓕` of size `i`. -/
def level (𝓕 : Finset (Finset ℕ)) (i : ℕ) : Finset (Finset ℕ) := 𝓕.filter fun A ↦ #A = i

/-- The `g`-shadow of `𝓕`: all `g`-element subsets of members of `𝓕`. -/
def shadow (g : ℕ) (𝓕 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝓕.biUnion fun A ↦ A.powersetCard g

/-- The family of complements `range n \ A`, `A ∈ 𝓕`. -/
def complFamily (n : ℕ) (𝓕 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  𝓕.image fun A ↦ range n \ A

/-- `lcm (1, …, t)`. -/
def lcmUpTo (t : ℕ) : ℕ := (Finset.Icc 1 t).lcm id

/-- The paper's threshold `q(t) = 1 + t + lcm (1, …, t)`. -/
def qBound (t : ℕ) : ℕ := t + 1 + lcmUpTo t

/-- `𝓕` is a family of `h`-element subsets of `range n`. -/
def IsUniformOn (n h : ℕ) (𝓕 : Finset (Finset ℕ)) : Prop := ∀ A ∈ 𝓕, A ⊆ range n ∧ #A = h

/-- The containment row of `A`: the indicator, on the `g`-subsets of `range n`, of `S ⊆ A`. -/
def inclVec (n g : ℕ) (A : Finset ℕ) : (range n).powersetCard g → ℚ :=
  fun S ↦ if (S : Finset ℕ) ⊆ A then 1 else 0

lemma mem_level {𝓕 : Finset (Finset ℕ)} {i : ℕ} {A : Finset ℕ} :
    A ∈ level 𝓕 i ↔ A ∈ 𝓕 ∧ #A = i := by
  simp [level]

lemma mem_shadow {g : ℕ} {𝓕 : Finset (Finset ℕ)} {G : Finset ℕ} :
    G ∈ shadow g 𝓕 ↔ ∃ A ∈ 𝓕, G ⊆ A ∧ #G = g := by
  simp [shadow, mem_powersetCard]

/-- Members of size `t` are excluded, since `#(A ∩ A) = #A`. -/
theorem level_eq_empty_of_avoids {t : ℕ} {𝓕 : Finset (Finset ℕ)}
    (hav : Erdos703.AvoidsRIntersection t 𝓕) : level 𝓕 t = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro A hA
  rw [mem_level] at hA
  exact hav A hA.1 A hA.1 (by rw [Finset.inter_self, hA.2])

/-- Trivial bound `f_i ≤ C(n, i)` for a family of subsets of `range n`. -/
theorem level_card_le_choose (n i : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) : #(level 𝓕 i) ≤ n.choose i := by
  have hsub : level 𝓕 i ⊆ (range n).powersetCard i := by
    intro A hA
    rw [mem_level] at hA
    exact Finset.mem_powersetCard.mpr ⟨h𝓕 A hA.1, hA.2⟩
  calc #(level 𝓕 i) ≤ #((range n).powersetCard i) := Finset.card_le_card hsub
    _ = n.choose i := by rw [Finset.card_powersetCard, Finset.card_range]

/-- Proposition 3.1 of Frankl–Füredi together with its counting consequence: for `t < i ≤ n + t`,
the `(i - t)`-shadow of `𝓕_i` and the complements of `𝓕_{n + t - i}` are disjoint families of
`(i - t)`-subsets of `range n`, hence `#∂_{i-t} 𝓕_i + f_{n+t-i} ≤ C(n, i - t)`. (The bound
`i ≤ n + t` is needed because of truncated subtraction; it is automatic for member sizes.) -/
theorem shadow_card_add_level_card_le (n t i : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (hti : t < i)
    (hin : i ≤ n + t) :
    #(shadow (i - t) (level 𝓕 i)) + #(level 𝓕 (n + t - i)) ≤ n.choose (i - t) := by
  classical
  set S₁ : Finset (Finset ℕ) := shadow (i - t) (level 𝓕 i) with hS₁
  set S₂ : Finset (Finset ℕ) := complFamily n (level 𝓕 (n + t - i)) with hS₂
  have hcompl : ∀ B ∈ level 𝓕 (n + t - i), B ⊆ range n ∧ #B = n + t - i := by
    intro B hB
    rw [mem_level] at hB
    exact ⟨h𝓕 B hB.1, hB.2⟩
  have hcard₂ : #S₂ = #(level 𝓕 (n + t - i)) := by
    rw [hS₂, complFamily]
    refine Finset.card_image_of_injOn ?_
    intro A hA B hB hAB
    have hA' : A ⊆ range n := (hcompl A hA).1
    have hB' : B ⊆ range n := (hcompl B hB).1
    have hAB' : range n \ A = range n \ B := hAB
    calc A = range n \ (range n \ A) := (Finset.sdiff_sdiff_eq_self hA').symm
      _ = range n \ (range n \ B) := by rw [hAB']
      _ = B := Finset.sdiff_sdiff_eq_self hB'
  have hsub₁ : S₁ ⊆ (range n).powersetCard (i - t) := by
    intro G hG
    rw [hS₁, mem_shadow] at hG
    obtain ⟨A, hA, hGA, hGcard⟩ := hG
    rw [mem_level] at hA
    exact Finset.mem_powersetCard.mpr ⟨hGA.trans (h𝓕 A hA.1), hGcard⟩
  have hsub₂ : S₂ ⊆ (range n).powersetCard (i - t) := by
    intro G hG
    rw [hS₂, complFamily, Finset.mem_image] at hG
    obtain ⟨B, hB, rfl⟩ := hG
    obtain ⟨hBsub, hBcard⟩ := hcompl B hB
    refine Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.card_sdiff_of_subset hBsub, Finset.card_range, hBcard]
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro G hG₁ hG₂
    rw [hS₁, mem_shadow] at hG₁
    obtain ⟨A, hA, hGA, hGcard⟩ := hG₁
    rw [mem_level] at hA
    obtain ⟨hA𝓕, hAcard⟩ := hA
    rw [hS₂, complFamily, Finset.mem_image] at hG₂
    obtain ⟨B, hB, hGB⟩ := hG₂
    have hB𝓕 : B ∈ 𝓕 := (mem_level.mp hB).1
    have hAsub : A ⊆ range n := h𝓕 A hA𝓕
    have hBA : B ∩ A = A \ G := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hxB, hxA⟩
        refine ⟨hxA, ?_⟩
        rw [← hGB]
        simp only [Finset.mem_sdiff, not_and, not_not]
        exact fun _ ↦ hxB
      · rintro ⟨hxA, hxG⟩
        refine ⟨?_, hxA⟩
        rw [← hGB] at hxG
        simp only [Finset.mem_sdiff, not_and, not_not] at hxG
        exact hxG (hAsub hxA)
    refine hav B hB𝓕 A hA𝓕 ?_
    rw [hBA, Finset.card_sdiff_of_subset hGA, hAcard, hGcard]
    omega
  calc #S₁ + #(level 𝓕 (n + t - i)) = #S₁ + #S₂ := by rw [hcard₂]
    _ = #(S₁ ∪ S₂) := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #((range n).powersetCard (i - t)) :=
        Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
    _ = n.choose (i - t) := by rw [Finset.card_powersetCard, Finset.card_range]

/-- Every `m > lcm (1, …, t)` has a prime-power divisor exceeding `t`
(otherwise every prime-power part of `m` divides the lcm, so `m` does). -/
private lemma lcmUpTo_ne_zero (t : ℕ) : lcmUpTo t ≠ 0 := by
  rw [lcmUpTo, Ne, Finset.lcm_eq_zero_iff]
  rintro ⟨x, hx, hx0⟩
  rw [Finset.mem_Icc] at hx
  simp only [id_eq] at hx0
  omega

theorem exists_primePow_dvd_of_lcmUpTo_lt (t m : ℕ) (hm : lcmUpTo t < m) :
    ∃ p s : ℕ, p.Prime ∧ 0 < s ∧ p ^ s ∣ m ∧ t < p ^ s := by
  by_contra hcon
  have hcon' : ∀ p s : ℕ, p.Prime → 0 < s → p ^ s ∣ m → p ^ s ≤ t := by
    intro p s hp hs hps
    by_contra hlt
    exact hcon ⟨p, s, hp, hs, hps, Nat.lt_of_not_le hlt⟩
  have hL0 : lcmUpTo t ≠ 0 := lcmUpTo_ne_zero t
  have hm0 : m ≠ 0 := by omega
  have hdvd : m ∣ lcmUpTo t := by
    rw [← Nat.factorization_le_iff_dvd hm0 hL0, Finsupp.le_iff]
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hepos : 0 < m.factorization p :=
      hpp.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
    have hpe : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
    have hmem : p ^ m.factorization p ∈ Finset.Icc 1 t :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos, hcon' p _ hpp hepos hpe⟩
    have hdd : p ^ m.factorization p ∣ lcmUpTo t := Finset.dvd_lcm hmem
    exact (hpp.pow_dvd_iff_le_factorization hL0).mp hdd
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) hdvd
  omega

end FranklFuredi

end

/-! ### Upstream module `JSP573/FF/RankLemmas.lean` -/

/-!
# Frankl–Füredi 1984: arithmetic and polynomial lemmas for the Frankl–Singhi rank theorem

Three independent leaves used in the proof of Theorem 1.4 (appendix of the paper):

1. a binomial divisibility fact from Kummer's theorem: if `p ^ s ∣ k + 1` and `1 ≤ d < p ^ s`
   then `p ∣ C(k + d, k)`;
2. the Newton-series expansion of the degree-`(h - t - 1)` polynomial
   `ffPoly h t x = ∏_{t < i < h} (i - x) / (h - t - 1)!` in the basis
   `C(x, s) · C(h - s, h - t - 1 - s)`, `0 ≤ s ≤ h - t - 1`, together with its values;
3. clearing denominators and powers of `p` from a nonzero rational coefficient vector.
-/

namespace FranklFuredi

/-- Kummer: if `p ^ s ∣ k + 1` and `1 ≤ d < p ^ s` then adding `d` to `k` carries in base `p`,
so `p ∣ C(k + d, k)`. -/
theorem prime_dvd_choose_of_pow_dvd_succ (p s k d : ℕ) (hp : p.Prime) (hs : 0 < s)
    (hk : p ^ s ∣ k + 1) (hd1 : 1 ≤ d) (hd : d < p ^ s) : p ∣ (k + d).choose k := by
  have hp2 : 2 ≤ p := hp.two_le
  have hps : 0 < p ^ s := Nat.pow_pos (by omega)
  have hle : p ^ s ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) hk
  have hkd : p ^ s ≤ k + d := by omega
  obtain ⟨m, hm⟩ := hk
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hkeq : k = (p ^ s - 1) + p ^ s * (m - 1) := by
    have h1 : p ^ s * m = p ^ s * (m - 1) + p ^ s := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  have hkmod : k % p ^ s = p ^ s - 1 := by
    rw [hkeq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdmod : d % p ^ s = d := Nat.mod_eq_of_lt hd
  have hsb : s < Nat.log p (k + d) + 1 := by
    have : s ≤ Nat.log p (k + d) := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hkd
    omega
  have hmem : s ∈ {i ∈ Finset.Ico 1 (Nat.log p (k + d) + 1) |
      p ^ i ≤ k % p ^ i + (k + d - k) % p ^ i} := by
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.add_sub_cancel_left]
    exact ⟨⟨hs, hsb⟩, by rw [hkmod, hdmod]; omega⟩
  refine dvd_of_emultiplicity_pos ?_
  rw [hp.emultiplicity_choose (Nat.le_add_right k d) (Nat.lt_succ_self _)]
  exact_mod_cast Finset.card_pos.mpr ⟨s, hmem⟩

/-- The paper's polynomial `p(x) = ∏_{t < i < h} (i - x) / (h - t - 1)!`, as a function on `ℕ`
with rational values. -/
noncomputable def ffPoly (h t : ℕ) (x : ℕ) : ℚ :=
  (∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - x)) / ((h - t - 1).factorial : ℚ)

/-- For `t < x < h` the product contains the factor `x - x`. -/
theorem ffPoly_eq_zero (h t x : ℕ) (hx₁ : t < x) (hx₂ : x < h) : ffPoly h t x = 0 := by
  rw [ffPoly, Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨hx₁, hx₂⟩) (sub_self _), zero_div]

/-- For `x ≤ t < h` the defining product is a falling factorial. -/
private lemma prod_Ico_sub_eq_descFactorial (t x : ℕ) (hx : x ≤ t) (h : ℕ) (ht : t < h) :
    ∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - x) = ((h - 1 - x).descFactorial (h - t - 1) : ℚ) := by
  induction h, ht using Nat.le_induction with
  | base => simp
  | succ h ht ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ih]
    have e1 : h + 1 - 1 - x = h - 1 - x + 1 := by omega
    have e2 : h + 1 - t - 1 = h - t - 1 + 1 := by omega
    have e3 : ((h - 1 - x : ℕ) : ℚ) + 1 = (h : ℚ) - x := by
      have h1 : ((h - 1 - x : ℕ) : ℚ) = (h : ℚ) - x - 1 := by
        rw [Nat.cast_sub (by omega : x ≤ h - 1), Nat.cast_sub (by omega : 1 ≤ h)]
        push_cast
        ring
      rw [h1]; ring
    rw [e1, e2, Nat.succ_descFactorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, e3]
    ring

/-- For `x ≤ t` the value is the binomial coefficient `C(h - 1 - x, h - t - 1)`. -/
theorem ffPoly_eq_choose (h t x : ℕ) (ht : t < h) (hx : x ≤ t) :
    ffPoly h t x = ((h - 1 - x).choose (h - t - 1) : ℚ) := by
  have hfac : ((h - t - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (h - t - 1)).ne'
  rw [ffPoly, prod_Ico_sub_eq_descFactorial t x hx h ht, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_comm, mul_div_assoc, div_self hfac, mul_one]

/-- At `x = h` the value is `(-1) ^ (h - t - 1)`. -/
theorem ffPoly_at_top (h t : ℕ) (ht : t < h) : ffPoly h t h = (-1 : ℚ) ^ (h - t - 1) := by
  have hfac : ((h - t - 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (h - t - 1)).ne'
  have hcast : (h : ℚ) = (t : ℚ) + 1 + ((h - t - 1 : ℕ) : ℚ) := by
    have h1 : ((h - t - 1 : ℕ) : ℚ) = (h : ℚ) - t - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ h - t), Nat.cast_sub (by omega : t ≤ h)]
      push_cast
      ring
    rw [h1]; ring
  have key : ∏ i ∈ Finset.Ico (t + 1) h, ((i : ℚ) - h)
      = (-1 : ℚ) ^ (h - t - 1) * ((h - t - 1).factorial : ℚ) := by
    rw [Finset.prod_Ico_eq_prod_range]
    have hn : h - (t + 1) = h - t - 1 := by omega
    rw [hn]
    have step : ∀ j ∈ Finset.range (h - t - 1),
        ((t + 1 + j : ℕ) : ℚ) - (h : ℚ) = -1 * (((h - t - 1 - j : ℕ)) : ℚ) := by
      intro j hj
      have hjN : j < h - t - 1 := Finset.mem_range.mp hj
      rw [Nat.cast_sub hjN.le, hcast]
      push_cast
      ring
    rw [Finset.prod_congr rfl step, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
    congr 1
    rw [← Nat.cast_prod]
    congr 1
    have hrefl := Finset.prod_range_reflect (fun j ↦ j + 1) (h - t - 1)
    rw [Finset.prod_range_add_one_eq_factorial] at hrefl
    rw [← hrefl]
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have : j < h - t - 1 := Finset.mem_range.mp hj
    omega
  rw [ffPoly, key, mul_div_assoc, div_self hfac, mul_one]

/-- Iterated forward differences commute with restriction of a function on `ℚ` to `ℕ`. -/
private lemma fwdDiff_iter_natCast (k : ℕ) (F : ℚ → ℚ) (n : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (fun m : ℕ ↦ F (m : ℚ)) n = (fwdDiff (1 : ℚ))^[k] F (n : ℚ) := by
  induction k generalizing F with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hstep : (fwdDiff (1 : ℕ) fun m : ℕ ↦ F (m : ℚ))
        = fun m : ℕ ↦ (fwdDiff (1 : ℚ) F) (m : ℚ) := by
      funext m
      simp only [fwdDiff]
      push_cast
      ring_nf
    rw [hstep, ih]

/-- Iterated forward differences of the zero function vanish. -/
private lemma fwdDiff_iter_zero_fun (j : ℕ) : (fwdDiff (1 : ℚ))^[j] (0 : ℚ → ℚ) = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    simp [fwdDiff]

/-- Newton expansion: `ffPoly h t` is a polynomial of degree `h - t - 1` in `x`, so it is a
combination of `C(x, s) · C(h - s, h - t - 1 - s)`, `s ≤ h - t - 1` (the factors
`C(h - s, h - t - 1 - s)` are positive constants; the expansion coefficients are the forward
differences at `0`, see `shift_eq_sum_fwdDiff_iter` and
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`). -/
theorem exists_ffPoly_expansion (h t : ℕ) (ht : t < h) :
    ∃ α : ℕ → ℚ, ∀ x : ℕ, ffPoly h t x =
      ∑ s ∈ Finset.range (h - t), α s * (x.choose s : ℚ) * ((h - s).choose (h - t - 1 - s) : ℚ) := by
  classical
  set N := h - t - 1 with hN
  have hNt : h - t = N + 1 := by omega
  have hfac : ((N).factorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos N).ne'
  set P : Polynomial ℚ := Polynomial.C (((N).factorial : ℚ))⁻¹ *
    ∏ i ∈ Finset.Ico (t + 1) h, (Polynomial.C (i : ℚ) - Polynomial.X) with hP
  have hPeval : ∀ m : ℕ, P.eval (m : ℚ) = ffPoly h t m := by
    intro m
    rw [hP, ffPoly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X]
    rw [div_eq_inv_mul]
  have hdeg : P.natDegree < N + 1 := by
    have h1 : (∏ i ∈ Finset.Ico (t + 1) h,
        (Polynomial.C (i : ℚ) - Polynomial.X)).natDegree ≤
        ∑ _i ∈ Finset.Ico (t + 1) h, 1 := by
      refine (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have h2 : P.natDegree ≤ ∑ _i ∈ Finset.Ico (t + 1) h, 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans h1
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at h2
    omega
  have hzero : ∀ k, N + 1 ≤ k → (fwdDiff (1 : ℚ))^[k] (fun x ↦ P.eval x) = 0 := by
    intro k hk
    obtain ⟨j, hj⟩ : ∃ j, k = j + (N + 1) := ⟨k - (N + 1), by omega⟩
    rw [hj, Function.iterate_add_apply, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg,
      fwdDiff_iter_zero_fun]
  set β : ℕ → ℚ := fun k ↦ (fwdDiff (1 : ℕ))^[k] (ffPoly h t) 0 with hβ
  have hβzero : ∀ k, N + 1 ≤ k → β k = 0 := by
    intro k hk
    have hff : (fun m : ℕ ↦ P.eval (m : ℚ)) = ffPoly h t := funext hPeval
    have hval : β k = (fwdDiff (1 : ℚ))^[k] (fun x ↦ P.eval x) ((0 : ℕ) : ℚ) := by
      rw [hβ, ← hff]
      exact fwdDiff_iter_natCast k (fun x ↦ P.eval x) 0
    rw [hval, hzero k hk]
    rfl
  have newton : ∀ x : ℕ, ffPoly h t x = ∑ k ∈ Finset.range (x + 1), (x.choose k : ℚ) * β k := by
    intro x
    have := shift_eq_sum_fwdDiff_iter (1 : ℕ) (ffPoly h t) x 0
    simpa [hβ, nsmul_eq_mul] using this
  refine ⟨fun s ↦ β s / ((h - s).choose (h - t - 1 - s) : ℚ), fun x ↦ ?_⟩
  set M := max (x + 1) (N + 1) with hM
  have hsub1 : Finset.range (x + 1) ⊆ Finset.range M :=
    Finset.range_mono (le_max_left _ _)
  have hsub2 : Finset.range (N + 1) ⊆ Finset.range M :=
    Finset.range_mono (le_max_right _ _)
  have hL : ∑ k ∈ Finset.range (x + 1), (x.choose k : ℚ) * β k
      = ∑ k ∈ Finset.range M, (x.choose k : ℚ) * β k := by
    refine Finset.sum_subset hsub1 fun k _ hk ↦ ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
    simp
  have hterm : ∀ s ∈ Finset.range (h - t),
      (β s / ((h - s).choose (h - t - 1 - s) : ℚ)) * (x.choose s : ℚ) *
        ((h - s).choose (h - t - 1 - s) : ℚ) = (x.choose s : ℚ) * β s := by
    intro s hs
    have hs' : s < h - t := Finset.mem_range.mp hs
    have hpos : 0 < (h - s).choose (h - t - 1 - s) := Nat.choose_pos (by omega)
    have hne : ((h - s).choose (h - t - 1 - s) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hne]
    ring
  have hR : ∑ s ∈ Finset.range (h - t),
      (β s / ((h - s).choose (h - t - 1 - s) : ℚ)) * (x.choose s : ℚ) *
        ((h - s).choose (h - t - 1 - s) : ℚ)
      = ∑ k ∈ Finset.range M, (x.choose k : ℚ) * β k := by
    rw [Finset.sum_congr rfl hterm, show h - t = N + 1 from hNt]
    refine Finset.sum_subset hsub2 fun k _ hk ↦ ?_
    rw [hβzero k (by simpa using hk), mul_zero]
  rw [newton x, hL, ← hR]

/-- Divide a nonzero integer vector by the largest power of the prime `p` dividing all entries. -/
private lemma exists_pow_factor {ι : Type*} [Fintype ι] {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) (e : ι → ℤ), e ≠ 0 → ∑ i, (e i).natAbs ≤ n →
      ∃ (f : ι → ℤ) (k : ℕ), (∀ i, e i = (p : ℤ) ^ k * f i) ∧ ∃ i, ¬ (p : ℤ) ∣ f i := by
  intro n
  induction n with
  | zero =>
    intro e he hsum
    exact absurd (funext fun i ↦ by
      have h1 : (e i).natAbs ≤ ∑ j, (e j).natAbs :=
        Finset.single_le_sum (f := fun j ↦ (e j).natAbs) (fun j _ ↦ Nat.zero_le _)
          (Finset.mem_univ i)
      have h2 : (e i).natAbs = 0 := by omega
      simpa [Int.natAbs_eq_zero] using h2) he
  | succ n ih =>
    intro e he hsum
    by_cases hex : ∀ i, (p : ℤ) ∣ e i
    · have hef : ∀ i, e i = (p : ℤ) * (e i / (p : ℤ)) := fun i ↦ (Int.mul_ediv_cancel' (hex i)).symm
      have hfne : (fun i ↦ e i / (p : ℤ)) ≠ 0 := by
        intro h0
        exact he (funext fun i ↦ by rw [hef i, congrFun h0 i]; simp)
      have hnat : ∀ i, (e i).natAbs = p * (e i / (p : ℤ)).natAbs := by
        intro i
        conv_lhs => rw [hef i]
        simp [Int.natAbs_mul]
      have hsum' : ∑ i, (e i / (p : ℤ)).natAbs ≤ n := by
        have h1 : ∑ i, (e i).natAbs = p * ∑ i, (e i / (p : ℤ)).natAbs := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ hnat i
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hfne
        have h2 : 0 < ∑ j, (e j / (p : ℤ)).natAbs :=
          lt_of_lt_of_le (Int.natAbs_pos.mpr hi)
            (Finset.single_le_sum (f := fun j ↦ (e j / (p : ℤ)).natAbs)
              (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i))
        have h3 : 2 * ∑ j, (e j / (p : ℤ)).natAbs ≤ p * ∑ j, (e j / (p : ℤ)).natAbs :=
          Nat.mul_le_mul_right _ hp.two_le
        omega
      obtain ⟨g, k, hg, hgi⟩ := ih (fun i ↦ e i / (p : ℤ)) hfne hsum'
      exact ⟨g, k + 1, fun i ↦ by rw [hef i, hg i]; ring, hgi⟩
    · obtain ⟨i, hi⟩ := not_forall.mp hex
      exact ⟨e, 0, by simp, ⟨i, hi⟩⟩

/-- A nonzero rational vector can be rescaled to an integer vector, not all of whose entries are
divisible by the prime `p`, by clearing denominators and then dividing out powers of `p`. -/
theorem exists_int_rescale_not_all_dvd {ι : Type*} [Fintype ι] (p : ℕ) (hp : p.Prime)
    (c : ι → ℚ) (hc : c ≠ 0) :
    ∃ (d : ι → ℤ) (L : ℚ), L ≠ 0 ∧ (∀ i, (d i : ℚ) = L * c i) ∧ ∃ i, ¬ (p : ℤ) ∣ d i := by
  classical
  set L₀ : ℕ := ∏ i, (c i).den with hL₀
  have hL₀pos : 0 < L₀ := by
    refine Nat.pos_of_ne_zero fun h0 ↦ ?_
    rw [hL₀, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    exact (c i).den_pos.ne' hi
  have hL₀q : ((L₀ : ℚ)) ≠ 0 := by exact_mod_cast hL₀pos.ne'
  have hex : ∀ i, ∃ z : ℤ, (z : ℚ) = (L₀ : ℚ) * c i := by
    intro i
    obtain ⟨m, hm⟩ : ((c i).den : ℤ) ∣ (L₀ : ℤ) := by
      exact_mod_cast Int.natCast_dvd_natCast.mpr
        (Finset.dvd_prod_of_mem (fun j ↦ (c j).den) (Finset.mem_univ i))
    have hmq : (L₀ : ℚ) = ((c i).den : ℚ) * (m : ℚ) := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hm
    refine ⟨m * (c i).num, ?_⟩
    calc ((m * (c i).num : ℤ) : ℚ) = (m : ℚ) * (c i * ((c i).den : ℚ)) := by
          rw [Rat.mul_den_eq_num]
          push_cast
          ring
      _ = ((c i).den : ℚ) * (m : ℚ) * c i := by ring
      _ = (L₀ : ℚ) * c i := by rw [← hmq]
  choose e he using hex
  have hene : e ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
    intro h0
    apply hi
    have h1 : (0 : ℚ) = (L₀ : ℚ) * c i := by
      rw [← he i, show e i = 0 from congrFun h0 i]
      simp
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hL₀q
    · exact h
  obtain ⟨f, k, hf, i₀, hi₀⟩ := exists_pow_factor hp (∑ i, (e i).natAbs) e hene le_rfl
  have hpq : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.pos.ne')
  refine ⟨f, (L₀ : ℚ) / ((p : ℚ)) ^ k, div_ne_zero hL₀q hpq, fun i ↦ ?_, ⟨i₀, hi₀⟩⟩
  have h1 : ((e i : ℤ) : ℚ) = ((p : ℚ)) ^ k * (f i : ℚ) := by
    rw [hf i]
    push_cast
    ring
  rw [div_mul_eq_mul_div, ← he i, h1]
  field_simp

end FranklFuredi

/-! ### Upstream module `JSP573/FF/FranklSinghi.lean` -/

section
/-!
# Frankl–Füredi 1984, Theorem 1.4 (Frankl–Singhi): full row rank of the containment matrix

Let `𝓕` be a family of `h`-subsets of `range n` with `#(A ∩ B) ≠ t` for all distinct
`A, B ∈ 𝓕`, and suppose `h - t` has a prime-power divisor `p ^ s > t`. Then the rows
`inclVec n (h - t - 1) A`, `A ∈ 𝓕`, are linearly independent over `ℚ`.

Proof (appendix of the paper). Suppose `∑_A c_A · inclVec A = 0` with `c ≠ 0`; rescale to integers
`c_A` not all divisible by `p` (`exists_int_rescale_not_all_dvd`) and fix `A₁` with `p ∤ c_{A₁}`.
Summing the relation over the `(h - t - 1)`-sets `T ⊇ S` gives, for every `S` with `#S = s`,
`∑_{A ⊇ S} c_A · C(h - s, h - t - 1 - s) = 0` (11); summing over the `s`-subsets `S` of `A₁` gives
`∑_A c_A · C(#(A ∩ A₁), s) · C(h - s, h - t - 1 - s) = 0` (12) for every `s ≤ h - t - 1`.
Combining (12) with the coefficients of `exists_ffPoly_expansion` yields
`∑_A c_A · ffPoly h t (#(A ∩ A₁)) = 0`. For `A ≠ A₁`, `#(A ∩ A₁) ∈ [0, h - 1] \ {t}`: the value is
`0` for `t < #(A ∩ A₁) < h` (`ffPoly_eq_zero`) and `C(h - 1 - j, h - t - 1)` for `j ≤ t - 1`,
which is divisible by `p` (`ffPoly_eq_choose`, `prime_dvd_choose_of_pow_dvd_succ` with
`k = h - t - 1`, `d = t - j`); for `A = A₁` it is `(-1) ^ (h - t - 1)` (`ffPoly_at_top`). Reducing
the integer identity modulo `p` gives `p ∣ c_{A₁}`, a contradiction.
-/

open _root_.Finset

namespace FranklFuredi

/-- The integral value of `ffPoly h t (#(B ∩ C))` on `h`-sets `B` meeting the fixed `h`-set `C`
in a number of points different from `t`: `(-1) ^ (h - t - 1)` at `B = C`, `0` when
`t < #(B ∩ C)`, and `C(h - 1 - #(B ∩ C), h - t - 1)` when `#(B ∩ C) < t`. -/
private def wt (h t : ℕ) (C B : Finset ℕ) : ℤ :=
  if B = C then (-1) ^ (h - t - 1)
  else if t < #(B ∩ C) then 0 else ((h - 1 - #(B ∩ C)).choose (h - t - 1) : ℤ)

/-- `wt` indeed computes `ffPoly h t (#(B ∩ C))` on such a set `B`. -/
private lemma wt_cast (h t : ℕ) (ht : t < h) (C B : Finset ℕ) (hB : #B = h) (hC : #C = h)
    (hne : B ≠ C → #(B ∩ C) ≠ t) : ((wt h t C B : ℤ) : ℚ) = ffPoly h t (#(B ∩ C)) := by
  unfold wt
  by_cases hBC : B = C
  · subst hBC
    rw [ite_eq_left rfl, Finset.inter_self, hB, ffPoly_at_top h t ht]
    push_cast
    ring
  · rw [ite_eq_right hBC]
    have hsub : B ∩ C ⊆ C := Finset.inter_subset_right
    have hle : #(B ∩ C) ≤ h := hC ▸ Finset.card_le_card hsub
    have hlt : #(B ∩ C) < h := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact hlt
      · refine absurd ?_ hBC
        have h1 : B ∩ C = C := Finset.eq_of_subset_of_card_le hsub (by omega)
        exact (Finset.eq_of_subset_of_card_le (h1 ▸ Finset.inter_subset_left) (by omega)).symm
    rcases lt_trichotomy (#(B ∩ C)) t with hj | hj | hj
    · rw [ite_eq_right (by omega), ffPoly_eq_choose h t _ ht hj.le]
      push_cast
      ring
    · exact absurd hj (hne hBC)
    · rw [ite_eq_left hj, ffPoly_eq_zero h t _ hj hlt]
      norm_num

/-- Away from the distinguished set `C`, the prime `p` divides `wt`. -/
private lemma prime_dvd_wt (p s h t : ℕ) (hp : p.Prime) (hs : 0 < s) (hdiv : p ^ s ∣ h - t)
    (hq : t < p ^ s) (ht : t < h) (C B : Finset ℕ) (hBC : B ≠ C) (hnt : #(B ∩ C) ≠ t) :
    (p : ℤ) ∣ wt h t C B := by
  unfold wt
  rw [ite_eq_right hBC]
  by_cases hj : t < #(B ∩ C)
  · rw [ite_eq_left hj]
    exact dvd_zero _
  · rw [ite_eq_right hj]
    have hk : p ^ s ∣ (h - t - 1) + 1 := by
      rwa [show h - t - 1 + 1 = h - t by omega]
    have hidx : h - 1 - #(B ∩ C) = (h - t - 1) + (t - #(B ∩ C)) := by omega
    rw [hidx]
    exact_mod_cast prime_dvd_choose_of_pow_dvd_succ p s (h - t - 1) (t - #(B ∩ C)) hp hs hk
      (by omega) (by omega)

/-- Theorem 1.4 (Frankl–Singhi). -/
theorem frankl_singhi (n h t p s : ℕ) (hp : p.Prime) (hs : 0 < s) (hdiv : p ^ s ∣ h - t)
    (hq : t < p ^ s) (ht : t < h) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (hav : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → #(A ∩ B) ≠ t) :
    LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A) := by
  rw [Fintype.linearIndependent_iff]
  intro c hrel A₀
  by_contra hA₀
  have hcne : c ≠ 0 := fun hc ↦ hA₀ (by simp [hc])
  obtain ⟨d, L, hL, hdL, A₁, hA₁⟩ := exists_int_rescale_not_all_dvd p hp c hcne
  obtain ⟨h1n, h1h⟩ := hU _ A₁.2
  have key : ∀ T : Finset ℕ, T ⊆ range n → #T = h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0) = 0 := by
    intro T hT1 hT2
    have hTm : T ∈ (range n).powersetCard (h - t - 1) := Finset.mem_powersetCard.2 ⟨hT1, hT2⟩
    have h0 := congrFun hrel ⟨T, hTm⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, inclVec] at h0
    have hfac : ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0)
        = L * ∑ A : 𝓕, c A * (if T ⊆ (A : Finset ℕ) then 1 else 0) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun A _ ↦ by rw [hdL A]; ring
    rw [hfac, h0, mul_zero]
  have h11 : ∀ S : Finset ℕ, S ⊆ range n → #S ≤ h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
        * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) = 0 := by
    intro S hS hSg
    have hz : ∑ T ∈ ((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T),
        ∑ A : 𝓕, (d A : ℚ) * (if T ⊆ (A : Finset ℕ) then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun T hT ↦ by
        rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
        exact key T hT.1.1 hT.1.2
    have hcnt : ∀ A : 𝓕, ∑ T ∈ ((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T),
        (if T ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
        = (if S ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
          * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) := by
      intro A
      obtain ⟨hAn, hAh⟩ := hU _ A.2
      rw [Finset.sum_boole]
      by_cases hSA : S ⊆ (A : Finset ℕ)
      · rw [ite_eq_left hSA, one_mul]
        have hset : (((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T)).filter
            (fun T ↦ T ⊆ (A : Finset ℕ))
            = ((A : Finset ℕ).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T) := by
          ext T
          simp only [Finset.mem_filter, Finset.mem_powersetCard]
          exact ⟨fun hx ↦ ⟨⟨hx.2, hx.1.1.2⟩, hx.1.2⟩,
            fun hx ↦ ⟨⟨⟨hx.1.1.trans hAn, hx.1.2⟩, hx.2⟩, hx.1.1⟩⟩
        rw [hset, Finset.card_filter_powersetCard_subset S _ _ hSA hSg, hAh]
      · rw [ite_eq_right hSA, zero_mul]
        have hset : (((range n).powersetCard (h - t - 1)).filter (fun T ↦ S ⊆ T)).filter
            (fun T ↦ T ⊆ (A : Finset ℕ)) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro T hT
          simp only [Finset.mem_filter] at hT
          exact hSA (hT.1.2.trans hT.2)
        rw [hset]
        simp
    rw [Finset.sum_comm] at hz
    refine Eq.trans ?_ hz
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [mul_assoc, ← hcnt A, Finset.mul_sum]
  have h12 : ∀ σ : ℕ, σ ≤ h - t - 1 →
      ∑ A : 𝓕, (d A : ℚ) * (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ)
        * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ) = 0 := by
    intro σ hσ
    have hz : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ, ∑ A : 𝓕,
        (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
          * (((h - #S).choose (h - t - 1 - #S) : ℕ) : ℚ) = 0 :=
      Finset.sum_eq_zero fun S hS ↦ by
        rw [Finset.mem_powersetCard] at hS
        exact h11 S (hS.1.trans h1n) (hS.2 ▸ hσ)
    have hz2 : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ, ∑ A : 𝓕,
        (d A : ℚ) * (if S ⊆ (A : Finset ℕ) then 1 else 0)
          * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ) = 0 := by
      refine Eq.trans ?_ hz
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      rw [(Finset.mem_powersetCard.1 hS).2]
    rw [Finset.sum_comm] at hz2
    refine Eq.trans ?_ hz2
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    have hcnt2 : ∑ S ∈ (A₁ : Finset ℕ).powersetCard σ,
        (if S ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)
        = (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ) := by
      rw [Finset.sum_boole]
      congr 1
      have hset : ((A₁ : Finset ℕ).powersetCard σ).filter (fun S ↦ S ⊆ (A : Finset ℕ))
          = ((A : Finset ℕ) ∩ (A₁ : Finset ℕ)).powersetCard σ := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
        tauto
      rw [hset, Finset.card_powersetCard]
    rw [← hcnt2, Finset.mul_sum, Finset.sum_mul]
  obtain ⟨α, hα⟩ := exists_ffPoly_expansion h t ht
  have hmain : ∑ A : 𝓕, (d A : ℚ) * ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))) = 0 := by
    have hstep : ∀ A : 𝓕, (d A : ℚ) * ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ)))
        = ∑ σ ∈ Finset.range (h - t), α σ * ((d A : ℚ)
            * (((#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))).choose σ : ℕ) : ℚ)
            * (((h - σ).choose (h - t - 1 - σ) : ℕ) : ℚ)) := by
      intro A
      rw [hα, Finset.mul_sum]
      exact Finset.sum_congr rfl fun σ _ ↦ by ring
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ hσ ↦ ?_
    rw [Finset.mem_range] at hσ
    rw [← Finset.mul_sum, h12 σ (by omega), mul_zero]
  have hcast : ∀ A : 𝓕, ((wt h t (A₁ : Finset ℕ) (A : Finset ℕ) : ℤ) : ℚ)
      = ffPoly h t (#((A : Finset ℕ) ∩ (A₁ : Finset ℕ))) := by
    intro A
    obtain ⟨hAn, hAh⟩ := hU _ A.2
    exact wt_cast h t ht _ _ hAh h1h fun hne ↦ hav _ A.2 _ A₁.2 hne
  have hZ : ∑ A : 𝓕, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) = 0 := by
    have h1 : ((∑ A : 𝓕, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) : ℤ) : ℚ) = 0 := by
      push_cast [hcast]
      exact hmain
    exact_mod_cast h1
  have hsplit : (p : ℤ) ∣ d A₁ * (-1) ^ (h - t - 1) := by
    have he : d A₁ * (-1) ^ (h - t - 1)
        + ∑ A ∈ Finset.univ.erase A₁, d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) = 0 := by
      have hw1 : wt h t (A₁ : Finset ℕ) (A₁ : Finset ℕ) = (-1) ^ (h - t - 1) := by
        simp [wt]
      rw [← hw1, Finset.add_sum_erase Finset.univ
        (fun A : 𝓕 ↦ d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ)) (Finset.mem_univ A₁)]
      exact hZ
    have hrest : (p : ℤ) ∣ ∑ A ∈ Finset.univ.erase A₁,
        d A * wt h t (A₁ : Finset ℕ) (A : Finset ℕ) :=
      Finset.dvd_sum fun A hA ↦ by
        have hne : (A : Finset ℕ) ≠ (A₁ : Finset ℕ) := fun hEq ↦
          Finset.ne_of_mem_erase hA (Subtype.ext hEq)
        exact Dvd.dvd.mul_left (prime_dvd_wt p s h t hp hs hdiv hq ht _ _ hne
          (hav _ A.2 _ A₁.2 hne)) _
    rw [eq_neg_of_add_eq_zero_left he]
    exact dvd_neg.2 hrest
  refine hA₁ ?_
  have hsq : ((-1 : ℤ) ^ (h - t - 1)) * ((-1 : ℤ) ^ (h - t - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hfin := hsplit.mul_right ((-1 : ℤ) ^ (h - t - 1))
  rwa [mul_assoc, hsq, mul_one] at hfin

end FranklFuredi

end

/-! ### Upstream module `JSP573/FF/Shadow.lean` -/

section
/-!
# Frankl–Füredi 1984, Theorem 1.5: a Katona-type shadow inequality under full row rank

Let `𝓕` be a family of `h`-subsets of `range n` whose containment rows
`inclVec n (h - t - 1) A` are linearly independent over `ℚ`, with `t + 1 ≤ h`. Then for every
`g` with `h - t - 1 ≤ g ≤ h`,
`#𝓕 · C(2h - t - 1, g) ≤ #(shadow g 𝓕) · C(2h - t - 1, h)`
(Katona's bound, which for intersecting families needs `#(A ∩ B) ≥ t + 1`; here the rank
hypothesis replaces the intersection condition).

Proof (Section 2 of the paper), by induction on `h` with `g` and `t` decreasing together.
* Base `g = h - t - 1`: linearly independent rows, restricted to the columns `G ∈ shadow g 𝓕`
  (all other columns are zero), give `#𝓕 ≤ #(shadow g 𝓕)`; and
  `C(2h - t - 1, h - t - 1) = C(2h - t - 1, h)`.
* Step `g ≥ h - t` (so `t ≥ 1` unless `g = h`, which is trivial): for `x ∈ range n` the link
  `link 𝓕 x = {A \ {x} : x ∈ A ∈ 𝓕}` is `(h - 1)`-uniform, its containment rows for the parameter
  `(h - 1) - (t - 1) - 1 = h - t - 1` are again independent (Proposition 2.1: a vanishing
  combination of the link rows lifts, with the same coefficients on `A = B ∪ {x}`, to a vanishing
  combination of the rows of `𝓕`; for a column `G ∌ x` this is immediate and for `G ∋ x` one
  averages over the `t + 1` ways of extending `G \ {x}`), so the induction hypothesis applies
  with `(h - 1, t - 1, g - 1)`. Double counting: `∑_x #(link 𝓕 x) = h · #𝓕` and
  `∑_x #(shadow (g - 1) (link 𝓕 x)) ≤ g · #(shadow g 𝓕)`. Then
  `C(N - 1, g - 1) · N / g = C(N, g)` and `C(N - 1, h - 1) · N / h = C(N, h)` with
  `N = 2h - t - 1` give the claim.
-/

open _root_.Finset

namespace FranklFuredi

/-- The link of `𝓕` at `x`: `{A \ {x} : x ∈ A ∈ 𝓕}`. -/
def link (𝓕 : Finset (Finset ℕ)) (x : ℕ) : Finset (Finset ℕ) :=
  (𝓕.filter fun A ↦ x ∈ A).image fun A ↦ A.erase x

/-- Membership in the link: `B ∈ link 𝓕 x` iff `x ∉ B` and `insert x B ∈ 𝓕`. -/
private lemma mem_link {𝓕 : Finset (Finset ℕ)} {x : ℕ} {B : Finset ℕ} :
    B ∈ link 𝓕 x ↔ x ∉ B ∧ insert x B ∈ 𝓕 := by
  simp only [link, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨A, ⟨hA, hxA⟩, rfl⟩
    exact ⟨Finset.notMem_erase _ _, by rwa [Finset.insert_erase hxA]⟩
  · rintro ⟨hx, hA⟩
    exact ⟨insert x B, ⟨hA, Finset.mem_insert_self _ _⟩, Finset.erase_insert hx⟩

/-- Reindexing a sum over the link as a sum over the members of `𝓕` containing `x`. -/
private lemma sum_link {M : Type*} [AddCommMonoid M] {𝓕 : Finset (Finset ℕ)} {x : ℕ}
    (f : Finset ℕ → M) :
    ∑ B ∈ link 𝓕 x, f (insert x B) = ∑ A ∈ 𝓕.filter fun A ↦ x ∈ A, f A := by
  classical
  rw [link, Finset.sum_image]
  · exact Finset.sum_congr rfl fun A hA ↦ by
      rw [Finset.insert_erase (Finset.mem_filter.1 hA).2]
  · intro A hA A' hA' hAA'
    rw [Finset.mem_coe, Finset.mem_filter] at hA hA'
    have h2 : insert x (A.erase x) = insert x (A'.erase x) := congrArg (insert x) hAA'
    rwa [Finset.insert_erase hA.2, Finset.insert_erase hA'.2] at h2

/-- Independence of the containment rows, restated as: the only family of coefficients killing
every column indexed by a `k`-subset of `range n` is the zero family. -/
private lemma linearIndependent_inclVec_iff (n k : ℕ) (𝓖 : Finset (Finset ℕ)) :
    LinearIndependent ℚ (fun A : 𝓖 ↦ inclVec n k (A : Finset ℕ)) ↔
      ∀ c : Finset ℕ → ℚ,
        (∀ G ⊆ range n, #G = k → ∑ A ∈ 𝓖, (if G ⊆ A then c A else 0) = 0) → ∀ A ∈ 𝓖, c A = 0 := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro H c hc A hA
    refine H (fun A ↦ c (A : Finset ℕ)) ?_ ⟨A, hA⟩
    funext G
    have hG := mem_powersetCard.1 G.2
    have h3 := hc (G : Finset ℕ) hG.1 hG.2
    rw [← Finset.sum_coe_sort 𝓖 fun A ↦ if (G : Finset ℕ) ⊆ A then c A else 0] at h3
    simpa only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero] using h3
  · intro H a ha i
    have key : ∀ G ⊆ range n, #G = k →
        ∑ A ∈ 𝓖, (if G ⊆ A then (if hA : A ∈ 𝓖 then a ⟨A, hA⟩ else 0) else 0) = 0 := by
      intro G hGr hGk
      have h2 := congrFun ha ⟨G, mem_powersetCard.2 ⟨hGr, hGk⟩⟩
      have h3 : ∑ i : 𝓖, (if G ⊆ (i : Finset ℕ) then a i else 0) = 0 := by
        simpa only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
          mul_one, mul_zero] using h2
      rw [← Finset.sum_coe_sort 𝓖 fun A ↦ if G ⊆ A then (if hA : A ∈ 𝓖 then a ⟨A, hA⟩ else 0)
        else 0]
      exact Eq.trans (Finset.sum_congr rfl fun i _ ↦ by simp [i.2]) h3
    simpa [i.2] using H _ key i.1 i.2

/-- Proposition 2.1: independence of the containment rows passes to links (with `t - 1`). -/
theorem linearIndependent_link (n h t : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (ht : 1 ≤ t) (hth : t + 1 ≤ h)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A)) (x : ℕ) :
    LinearIndependent ℚ (fun B : link 𝓕 x ↦ inclVec n ((h - 1) - (t - 1) - 1) B) := by
  classical
  have hkk : h - 1 - (t - 1) - 1 = h - t - 1 := by omega
  rw [hkk, linearIndependent_inclVec_iff]
  rw [linearIndependent_inclVec_iff] at hli
  set k := h - t - 1 with hkdef
  intro a ha B hB
  set c : Finset ℕ → ℚ := fun A ↦ if x ∈ A then a (A.erase x) else 0 with hcdef
  have hcolx : ∀ G ⊆ range n, #G = k → x ∉ G → ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) = 0 := by
    intro G hGr hGk hxG
    have e1 : ∑ A ∈ 𝓕.filter (fun A ↦ x ∈ A), (if G ⊆ A then c A else 0)
        = ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun A hA hA' ↦ ?_
      have hxA : x ∉ A := by simpa [Finset.mem_filter, hA] using hA'
      simp [hcdef, hxA]
    rw [← e1, ← sum_link (fun A ↦ if G ⊆ A then c A else 0)]
    refine Eq.trans (Finset.sum_congr rfl fun B hB ↦ ?_) (ha G hGr hGk)
    rw [mem_link] at hB
    simp [hcdef, Finset.erase_insert hB.1, Finset.subset_insert_iff_of_notMem hxG]
  have hcol : ∀ G ⊆ range n, #G = k → ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0) = 0 := by
    intro G hGr hGk
    by_cases hxG : x ∈ G
    swap
    · exact hcolx G hGr hGk hxG
    have key : ((t : ℚ) + 1) * ∑ A ∈ 𝓕, (if G ⊆ A then c A else 0)
        = ∑ y ∈ range n \ G, ∑ A ∈ 𝓕, (if insert y G ⊆ A then c A else 0) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun A hA ↦ ?_
      by_cases hGA : G ⊆ A
      · have hAr : A ⊆ range n := (hU A hA).1
        have hAh : #A = h := (hU A hA).2
        have hinter : (range n \ G) ∩ A = A \ G := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_range]
          constructor
          · rintro ⟨⟨-, h2⟩, h3⟩
            exact ⟨h3, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨Finset.mem_range.1 (hAr h1), h2⟩, h1⟩
        have hcard : #(A \ G) = t + 1 := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.2 hGA, hAh, hGk]
          omega
        have e2 : ∑ y ∈ range n \ G, (if insert y G ⊆ A then c A else 0)
            = ∑ y ∈ (range n \ G) ∩ A, c A := by
          rw [← Finset.sum_ite_mem]
          exact Finset.sum_congr rfl fun y _ ↦ by simp [Finset.insert_subset_iff, hGA]
        have e3 : (if G ⊆ A then c A else 0) = c A := by simp [hGA]
        rw [e2, hinter, Finset.sum_const, hcard, nsmul_eq_mul, e3]
        push_cast
        ring
      · simp [hGA, Finset.insert_subset_iff]
    have hzero : ∀ y ∈ range n \ G, ∑ A ∈ 𝓕, (if insert y G ⊆ A then c A else 0) = 0 := by
      intro y hy
      rw [Finset.mem_sdiff, Finset.mem_range] at hy
      have hxmem : x ∈ insert y G := Finset.mem_insert_of_mem hxG
      set G' := (insert y G).erase x with hG'
      have hins : insert x G' = insert y G := Finset.insert_erase hxmem
      have hxG' : x ∉ G' := Finset.notMem_erase _ _
      have hG'r : G' ⊆ range n := (Finset.erase_subset _ _).trans (by
        rw [Finset.insert_subset_iff]
        exact ⟨Finset.mem_range.2 hy.1, hGr⟩)
      have hG'k : #G' = k := by
        rw [hG', Finset.card_erase_of_mem hxmem, Finset.card_insert_of_notMem hy.2, hGk]
        omega
      refine Eq.trans (Finset.sum_congr rfl fun A _ ↦ ?_) (hcolx G' hG'r hG'k hxG')
      by_cases hxA : x ∈ A
      · have hiff : insert y G ⊆ A ↔ G' ⊆ A := by
          rw [← hins, Finset.insert_subset_iff]
          simp [hxA]
        simp only [hiff]
      · simp [hcdef, hxA]
    have h0 := key.trans (Finset.sum_eq_zero hzero)
    have ht1 : ((t : ℚ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.1 h0).resolve_left ht1
  have hcz := hli c hcol (insert x B) (mem_link.1 hB).2
  simpa [hcdef, Finset.erase_insert (mem_link.1 hB).1] using hcz

/-- Base case of Theorem 1.5: independent rows give `#𝓕 ≤ #(shadow (h - t - 1) 𝓕)`. -/
theorem card_le_card_shadow_of_linearIndependent (n h t : ℕ) (𝓕 : Finset (Finset ℕ))
    (_hU : IsUniformOn n h 𝓕)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A)) :
    #𝓕 ≤ #(shadow (h - t - 1) 𝓕) := by
  classical
  set k := h - t - 1 with hk
  have key : LinearIndependent ℚ (fun A : 𝓕 ↦ (fun G : (shadow k 𝓕 : Finset (Finset ℕ)) ↦
      if (G : Finset ℕ) ⊆ (A : Finset ℕ) then (1 : ℚ) else 0)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fintype.linearIndependent_iff] at hli
    refine hli a ?_
    funext G
    have hG : #(G : Finset ℕ) = k := (mem_powersetCard.1 G.2).2
    simp only [Pi.zero_apply, Finset.sum_apply, inclVec, Pi.smul_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    by_cases hGs : (G : Finset ℕ) ∈ shadow k 𝓕
    · have h2 := congrFun ha ⟨(G : Finset ℕ), hGs⟩
      simpa only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero] using h2
    · refine Finset.sum_eq_zero fun A _ ↦ ?_
      have hns : ¬ (G : Finset ℕ) ⊆ (A : Finset ℕ) :=
        fun hsub ↦ hGs (mem_shadow.2 ⟨A, A.2, hsub, hG⟩)
      simp [hns]
  have h1 := key.fintype_card_le_finrank
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using h1

/-- The `g`-shadow of a family of subsets of `range n` is `g`-uniform. -/
private lemma isUniformOn_shadow {n h g : ℕ} {𝓕 : Finset (Finset ℕ)} (hU : IsUniformOn n h 𝓕) :
    IsUniformOn n g (shadow g 𝓕) := by
  intro G hG
  obtain ⟨A, hA, hGA, hGg⟩ := mem_shadow.1 hG
  exact ⟨hGA.trans (hU A hA).1, hGg⟩

/-- The link of an `h`-uniform family is `(h - 1)`-uniform. -/
private lemma isUniformOn_link {n h : ℕ} {𝓕 : Finset (Finset ℕ)} (hU : IsUniformOn n h 𝓕)
    (x : ℕ) : IsUniformOn n (h - 1) (link 𝓕 x) := by
  intro B hB
  obtain ⟨hxB, hmem⟩ := mem_link.1 hB
  refine ⟨(Finset.subset_insert x B).trans (hU _ hmem).1, ?_⟩
  have hc := (hU _ hmem).2
  rw [Finset.card_insert_of_notMem hxB] at hc
  omega

/-- Double counting the incidences `x ∈ G ∈ 𝓖` for an `m`-uniform family on `range n`. -/
private lemma sum_card_filter_mem (n m : ℕ) (𝓖 : Finset (Finset ℕ)) (h𝓖 : IsUniformOn n m 𝓖) :
    ∑ x ∈ range n, #(𝓖.filter fun G ↦ x ∈ G) = m * #𝓖 := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have hin : ∀ G ∈ 𝓖, ∑ x ∈ range n, (if x ∈ G then 1 else 0) = m := by
    intro G hG
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (h𝓖 G hG).1, Finset.sum_const, smul_eq_mul,
      mul_one, (h𝓖 G hG).2]
  rw [Finset.sum_congr rfl hin, Finset.sum_const, smul_eq_mul, mul_comm]

/-- `∑_x #(link 𝓕 x) = h · #𝓕` for an `h`-uniform family. -/
private lemma sum_card_link (n h : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕) :
    ∑ x ∈ range n, #(link 𝓕 x) = h * #𝓕 := by
  classical
  have hcard : ∀ x : ℕ, #(link 𝓕 x) = #(𝓕.filter fun A ↦ x ∈ A) := by
    intro x
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
    exact sum_link (fun _ ↦ (1 : ℕ))
  simp only [hcard]
  exact sum_card_filter_mem n h 𝓕 hU

/-- `∑_x #(∂_{g-1} (link 𝓕 x)) ≤ g · #(∂_g 𝓕)`. -/
private lemma sum_card_shadow_link_le (n h g : ℕ) (𝓕 : Finset (Finset ℕ))
    (hU : IsUniformOn n h 𝓕) (hg : 1 ≤ g) :
    ∑ x ∈ range n, #(shadow (g - 1) (link 𝓕 x)) ≤ g * #(shadow g 𝓕) := by
  classical
  have hstep : ∀ x ∈ range n,
      #(shadow (g - 1) (link 𝓕 x)) ≤ #((shadow g 𝓕).filter fun G ↦ x ∈ G) := by
    intro x _
    refine Finset.card_le_card_of_injOn (fun G' ↦ insert x G') ?_ ?_
    · intro G' hG'
      obtain ⟨B, hB, hG'B, hG'g⟩ := mem_shadow.1 (Finset.mem_coe.1 hG')
      obtain ⟨hxB, hmem⟩ := mem_link.1 hB
      have hxG' : x ∉ G' := fun hx ↦ hxB (hG'B hx)
      refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_shadow.2 ⟨insert x B, hmem,
        Finset.insert_subset_insert x hG'B, ?_⟩, Finset.mem_insert_self _ _⟩)
      rw [Finset.card_insert_of_notMem hxG', hG'g]
      omega
    · intro G₁ h₁ G₂ h₂ heq
      obtain ⟨B₁, hB₁, hG₁B, -⟩ := mem_shadow.1 (Finset.mem_coe.1 h₁)
      obtain ⟨B₂, hB₂, hG₂B, -⟩ := mem_shadow.1 (Finset.mem_coe.1 h₂)
      have hx₁ : x ∉ G₁ := fun hx ↦ (mem_link.1 hB₁).1 (hG₁B hx)
      have hx₂ : x ∉ G₂ := fun hx ↦ (mem_link.1 hB₂).1 (hG₂B hx)
      rw [← Finset.erase_insert hx₁, ← Finset.erase_insert hx₂]
      exact congrArg (fun G ↦ G.erase x) heq
  calc ∑ x ∈ range n, #(shadow (g - 1) (link 𝓕 x))
      ≤ ∑ x ∈ range n, #((shadow g 𝓕).filter fun G ↦ x ∈ G) := Finset.sum_le_sum hstep
    _ = g * #(shadow g 𝓕) := sum_card_filter_mem n g _ (isUniformOn_shadow hU)

/-- Theorem 1.5 (Frankl–Füredi). -/
theorem shadow_card_mul_choose_ge (n h t g : ℕ) (𝓕 : Finset (Finset ℕ)) (hU : IsUniformOn n h 𝓕)
    (hli : LinearIndependent ℚ (fun A : 𝓕 ↦ inclVec n (h - t - 1) A))
    (hth : t + 1 ≤ h) (hg₁ : h - t - 1 ≤ g) (hg₂ : g ≤ h) :
    (#𝓕 : ℚ) * ((2 * h - t - 1).choose g : ℚ) ≤
      (#(shadow g 𝓕) : ℚ) * ((2 * h - t - 1).choose h : ℚ) := by
  revert t g 𝓕
  induction h using Nat.strong_induction_on with
  | _ h IH =>
  intro t g 𝓕 hU hli hth hg₁ hg₂
  by_cases hgh : g = h
  · rw [hgh]
    have hsub : 𝓕 ⊆ shadow h 𝓕 := fun A hA ↦
      mem_shadow.2 ⟨A, hA, Finset.Subset.refl A, (hU A hA).2⟩
    have hc : (#𝓕 : ℚ) ≤ (#(shadow h 𝓕) : ℚ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  by_cases hgb : g = h - t - 1
  · rw [hgb]
    have hNh : 2 * h - t - 1 - h = h - t - 1 := by omega
    have hchoose : (2 * h - t - 1).choose (h - t - 1) = (2 * h - t - 1).choose h := by
      rw [← hNh]
      exact Nat.choose_symm (by omega)
    rw [hchoose]
    have hc : (#𝓕 : ℚ) ≤ (#(shadow (h - t - 1) 𝓕) : ℚ) := by
      exact_mod_cast card_le_card_shadow_of_linearIndependent n h t 𝓕 hU hli
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have ht1 : 1 ≤ t := by omega
  have hg0 : 1 ≤ g := by omega
  have hexp : 2 * (h - 1) - (t - 1) - 1 = 2 * h - t - 2 := by omega
  have hIH : ∀ x ∈ range n,
      (#(link 𝓕 x) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
        (#(shadow (g - 1) (link 𝓕 x)) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    intro x _
    have hx := IH (h - 1) (by omega) (t - 1) (g - 1) (link 𝓕 x) (isUniformOn_link hU x)
      (linearIndependent_link n h t 𝓕 hU ht1 hth hli x) (by omega) (by omega) (by omega)
    rwa [hexp] at hx
  have hsum : (∑ x ∈ range n, (#(link 𝓕 x) : ℚ)) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
      (∑ x ∈ range n, (#(shadow (g - 1) (link 𝓕 x)) : ℚ)) *
        (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum hIH
  have e3 : (∑ x ∈ range n, (#(link 𝓕 x) : ℚ)) = (h : ℚ) * (#𝓕 : ℚ) := by
    rw [← Nat.cast_sum, sum_card_link n h 𝓕 hU]
    push_cast
    ring
  have e4 : (∑ x ∈ range n, (#(shadow (g - 1) (link 𝓕 x)) : ℚ))
      ≤ (g : ℚ) * (#(shadow g 𝓕) : ℚ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast sum_card_shadow_link_le n h g 𝓕 hU hg0
  have hsum' : (h : ℚ) * (#𝓕 : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ) ≤
      (g : ℚ) * (#(shadow g 𝓕) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ) := by
    rw [← e3]
    exact hsum.trans (mul_le_mul_of_nonneg_right e4 (by positivity))
  have hbg : (2 * h - t - 1) * ((2 * h - t - 2).choose (g - 1))
      = ((2 * h - t - 1).choose g) * g := by
    have h1 := Nat.add_one_mul_choose_eq (2 * h - t - 2) (g - 1)
    have e1 : 2 * h - t - 2 + 1 = 2 * h - t - 1 := by omega
    have e2 : g - 1 + 1 = g := by omega
    rwa [e1, e2] at h1
  have hbh : (2 * h - t - 1) * ((2 * h - t - 2).choose (h - 1))
      = ((2 * h - t - 1).choose h) * h := by
    have h1 := Nat.add_one_mul_choose_eq (2 * h - t - 2) (h - 1)
    have e1 : 2 * h - t - 2 + 1 = 2 * h - t - 1 := by omega
    have e2 : h - 1 + 1 = h := by omega
    rwa [e1, e2] at h1
  have hbg' : ((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)
      = (((2 * h - t - 1).choose g : ℕ) : ℚ) * (g : ℚ) := by exact_mod_cast congrArg Nat.cast hbg
  have hbh' : ((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)
      = (((2 * h - t - 1).choose h : ℕ) : ℚ) * (h : ℚ) := by exact_mod_cast congrArg Nat.cast hbh
  have hNpos : (0 : ℚ) ≤ ((2 * h - t - 1 : ℕ) : ℚ) := by positivity
  have step2 : (g : ℚ) * (h : ℚ) * ((#𝓕 : ℚ) * (((2 * h - t - 1).choose g : ℕ) : ℚ)) ≤
      (g : ℚ) * (h : ℚ) * ((#(shadow g 𝓕) : ℚ) * (((2 * h - t - 1).choose h : ℕ) : ℚ)) :=
    calc (g : ℚ) * (h : ℚ) * ((#𝓕 : ℚ) * (((2 * h - t - 1).choose g : ℕ) : ℚ))
        = (h : ℚ) * (#𝓕 : ℚ) * ((((2 * h - t - 1).choose g : ℕ) : ℚ) * (g : ℚ)) := by ring
      _ = (h : ℚ) * (#𝓕 : ℚ) *
            (((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)) := by
          rw [hbg']
      _ = ((2 * h - t - 1 : ℕ) : ℚ) *
            ((h : ℚ) * (#𝓕 : ℚ) * (((2 * h - t - 2).choose (g - 1) : ℕ) : ℚ)) := by ring
      _ ≤ ((2 * h - t - 1 : ℕ) : ℚ) * ((g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)) := by
          exact mul_le_mul_of_nonneg_left hsum' hNpos
      _ = (g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            (((2 * h - t - 1 : ℕ) : ℚ) * (((2 * h - t - 2).choose (h - 1) : ℕ) : ℚ)) := by ring
      _ = (g : ℚ) * (#(shadow g 𝓕) : ℚ) *
            ((((2 * h - t - 1).choose h : ℕ) : ℚ) * (h : ℚ)) := by rw [hbh']
      _ = (g : ℚ) * (h : ℚ) * ((#(shadow g 𝓕) : ℚ) * (((2 * h - t - 1).choose h : ℕ) : ℚ)) := by
          ring
  refine le_of_mul_le_mul_left step2 ?_
  have : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg0
  have : (0 : ℚ) < (h : ℚ) := by exact_mod_cast (by omega : 1 ≤ h)
  positivity

end FranklFuredi

end

/-! ### Upstream module `JSP573/FF/Counting.lean` -/

section
/-!
# Frankl–Füredi 1984, Section 3: the level inequalities

For a family `𝓕` of subsets of `range n` with `#(A ∩ B) ≠ t` for all `A, B ∈ 𝓕` (`t ≥ 1`),
write `f_i = #(level 𝓕 i)`.

* `level_inequality` (inequality (3) of the paper, integer form): for `qBound t ≤ i` and
  `2 i ≤ n + t`, `f_i · i + f_{n+t-i} · (i - t) ≤ C(n, i - t) · (i - t)`. It combines the
  disjointness count (`shadow_card_add_level_card_le`), the Frankl–Singhi rank theorem (applied to
  `level 𝓕 i`, which is `i`-uniform; `i - t > lcm(1..t)` supplies the prime-power divisor) and
  the shadow inequality with `g = i - t`, using `C(2i-t-1, i-t) · (i-t) = C(2i-t-1, i) · i`.
* `ffBound n t` is the closed form of `#𝓕*(n, t)`.
* `card_le_ffBound_add_middle`: `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} f_i` once
  `qBound t ≤ (n + t) / 2` (sum the level inequalities over the pairs `(i, n + t - i)`, use
  `f_i ≤ C(n, i)` for `i < t`, `f_t = 0`, the self-paired middle level for `n + t` even, and the
  trivial bound on the top levels).
* `card_forbidden_level`: if `A₀ ∈ 𝓕` with `t < #A₀`, then level `b` omits all the
  `C(#A₀, t) · C(n - #A₀, b - t)` sets `B` of size `b` with `#(B ∩ A₀) = t`.
-/

open _root_.Finset

namespace FranklFuredi

/-- The closed form of `#𝓕*(n, t)`: sets of size `< t`, sets of size `> (n + t) / 2`, and, when
`n + t` is even, the sets of size `(n + t) / 2` avoiding the fixed element `0`. -/
def ffBound (n t : ℕ) : ℕ :=
  (∑ i ∈ Finset.range t, n.choose i) + (∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i) +
    (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0)

/-- Counting the subsets of `range n` selected by a predicate that depends only on the
cardinality: the answer is the sum of the binomial coefficients over the admissible sizes. -/
private lemma card_powerset_filter_card (n : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    #((range n).powerset.filter fun A ↦ Q #A) = ∑ i ∈ (range (n + 1)).filter Q, n.choose i := by
  classical
  have hmem : ∀ A ∈ (range n).powerset.filter fun A ↦ Q #A, #A ∈ range (n + 1) := by
    intro A hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA
    have h := Finset.card_le_card hA.1
    rw [Finset.card_range] at h
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmem, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases hQ : Q i
  · rw [ite_eq_left hQ]
    have h : (((range n).powerset.filter fun A ↦ Q #A).filter fun A ↦ #A = i)
        = (range n).powersetCard i := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2 ▸ hQ⟩, h.2⟩⟩
    rw [h, Finset.card_powersetCard, Finset.card_range]
  · rw [ite_eq_right hQ, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro A hA h
    rw [Finset.mem_filter] at hA
    exact hQ (h ▸ hA.2)

/-- Binomial coefficients above `n` vanish, so `∑_{i < t} C(n, i)` only sees indices `≤ n`. -/
private lemma sum_filter_lt_choose (n t : ℕ) :
    ∑ i ∈ (range (n + 1)).filter (fun i ↦ i < t), n.choose i = ∑ i ∈ range t, n.choose i := by
  refine Finset.sum_subset (fun x hx ↦ ?_) (fun x hx hx' ↦ ?_)
  · rw [Finset.mem_filter] at hx
    exact Finset.mem_range.mpr hx.2
  · rw [Finset.mem_range] at hx
    have hxn : n < x := by
      by_contra hc
      exact hx' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hx⟩)
    exact Nat.choose_eq_zero_of_lt hxn

/-- The indices `i ≤ n` with `m < i` form `Ioc m n`. -/
private lemma filter_lt_range_eq_Ioc (n m : ℕ) :
    (range (n + 1)).filter (fun i ↦ m < i) = Finset.Ioc m n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  omega

/-- The subsets of `range n` of size `> (n + t) / 2` or `< t` are counted by the first two
summands of `ffBound n t`. -/
private lemma card_filter_big_or_small (n t : ℕ) :
    #((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t) =
      (∑ i ∈ range t, n.choose i) + ∑ i ∈ Finset.Ioc ((n + t) / 2) n, n.choose i := by
  classical
  have hdisj : Disjoint ((range (n + 1)).filter fun i ↦ (n + t) / 2 < i)
      ((range (n + 1)).filter fun i ↦ i < t) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter, Finset.mem_range] at hi hi'
    omega
  rw [card_powerset_filter_card n fun i ↦ (n + t) / 2 < i ∨ i < t, Finset.filter_or,
    Finset.sum_union hdisj, filter_lt_range_eq_Ioc, sum_filter_lt_choose]
  omega

/-- The subsets of `range n` of a given size avoiding `0` number `C(n - 1, m)`. -/
private lemma card_filter_notMem_zero (n m : ℕ) (hn : 1 ≤ n) :
    #((range n).powerset.filter fun A ↦ #A = m ∧ 0 ∉ A) = (n - 1).choose m := by
  classical
  have h : ((range n).powerset.filter fun A ↦ #A = m ∧ 0 ∉ A)
      = ((range n).erase 0).powersetCard m := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
      Finset.subset_erase]
    tauto
  rw [h, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_range.mpr hn),
    Finset.card_range]

/-- `#(franklFurediOdd n t) = ffBound n t` when `n + t` is odd. -/
theorem card_franklFurediOdd (n t : ℕ) (hodd : (n + t) % 2 = 1) :
    #(Erdos703.franklFurediOdd n t) = ffBound n t := by
  rw [Erdos703.franklFurediOdd, card_filter_big_or_small, ffBound,
    ite_eq_right (show ¬(n + t) % 2 = 0 by omega), Nat.add_zero]

/-- `#(franklFurediEven n t) = ffBound n t` when `n + t` is even and `1 ≤ n`. -/
theorem card_franklFurediEven (n t : ℕ) (hn : 1 ≤ n) (heven : (n + t) % 2 = 0) :
    #(Erdos703.franklFurediEven n t) = ffBound n t := by
  classical
  have hsplit : Erdos703.franklFurediEven n t =
      ((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t) ∪
        ((range n).powerset.filter fun A ↦ #A = (n + t) / 2 ∧ 0 ∉ A) := by
    rw [Erdos703.franklFurediEven, ← Finset.filter_or]
    refine Finset.filter_congr fun A hA ↦ ?_
    rw [Finset.mem_powerset] at hA
    have hAn : #A ≤ n := by
      have h := Finset.card_le_card hA
      rwa [Finset.card_range] at h
    rw [Finset.filter_ne']
    by_cases h0 : 0 ∈ A
    · have h1 : 1 ≤ #A := Finset.card_pos.mpr ⟨0, h0⟩
      rw [Finset.card_erase_of_mem h0]
      simp only [h0, not_true_eq_false, and_false, or_false]
      omega
    · rw [Finset.erase_eq_of_notMem h0]
      simp only [h0, not_false_eq_true, and_true]
      omega
  have hdisj : Disjoint ((range n).powerset.filter fun A ↦ (n + t) / 2 < #A ∨ #A < t)
      ((range n).powerset.filter fun A ↦ #A = (n + t) / 2 ∧ 0 ∉ A) := by
    rw [Finset.disjoint_left]
    intro A hA hA'
    rw [Finset.mem_filter, Finset.mem_powerset] at hA hA'
    have hAn : #A ≤ n := by
      have h := Finset.card_le_card hA.1
      rwa [Finset.card_range] at h
    obtain ⟨hA2, -⟩ := hA'.2
    have hA1 := hA.2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_filter_big_or_small,
    card_filter_notMem_zero n _ hn, ffBound, ite_eq_left heven]

/-- The binomial identity `C(2i - t - 1, i - t) · (i - t) = C(2i - t - 1, i) · i` for `t < i`. -/
private lemma choose_mul_sub (t i : ℕ) (hti : t < i) :
    (2 * i - t - 1).choose (i - t) * (i - t) = (2 * i - t - 1).choose i * i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = t + (k + 1) := ⟨i - t - 1, by omega⟩
  have h1 : 2 * (t + (k + 1)) - t - 1 = t + 2 * k + 1 := by omega
  have h2 : t + (k + 1) - t = k + 1 := by omega
  have h3 : t + (k + 1) = t + k + 1 := by omega
  have e1 : (t + 2 * k + 1) * (t + 2 * k).choose k = (t + 2 * k + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (t + 2 * k) k
  have e2 : (t + 2 * k + 1) * (t + 2 * k).choose (t + k)
      = (t + 2 * k + 1).choose (t + k + 1) * (t + k + 1) :=
    Nat.add_one_mul_choose_eq (t + 2 * k) (t + k)
  have e3 : (t + 2 * k).choose k = (t + 2 * k).choose (t + k) := by
    rw [← Nat.choose_symm (show k ≤ t + 2 * k by omega)]
    congr 1
    omega
  rw [h1, h2, h3, ← e1, ← e2, e3]

/-- Inequality (3): `f_i · i + f_{n+t-i} · (i - t) ≤ C(n, i - t) · (i - t)`. -/
theorem level_inequality (n t i : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hqi : qBound t ≤ i)
    (hi : 2 * i ≤ n + t) :
    #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) ≤ n.choose (i - t) * (i - t) := by
  have _ht : 0 < t := ht
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hti : t < i := by omega
  have hlt : lcmUpTo t < i - t := by omega
  obtain ⟨p, s, hp, hs, hdvd, hpt⟩ := exists_primePow_dvd_of_lcmUpTo_lt t (i - t) hlt
  have hU : IsUniformOn n i (level 𝓕 i) := by
    intro A hA
    rw [mem_level] at hA
    exact ⟨h𝓕 A hA.1, hA.2⟩
  have hav' : ∀ A ∈ level 𝓕 i, ∀ B ∈ level 𝓕 i, A ≠ B → #(A ∩ B) ≠ t := by
    intro A hA B hB _
    exact hav A (mem_level.mp hA).1 B (mem_level.mp hB).1
  have hli := frankl_singhi n i t p s hp hs hdvd hpt hti (level 𝓕 i) hU hav'
  have hshadow := shadow_card_mul_choose_ge n i t (i - t) (level 𝓕 i) hU hli (by omega)
    (by omega) (by omega)
  have hNpos : 0 < (2 * i - t - 1).choose i := Nat.choose_pos (by omega)
  have hitpos : (0 : ℚ) < ((i - t : ℕ) : ℚ) := by
    exact_mod_cast (show 0 < i - t by omega)
  have hcast : ((2 * i - t - 1).choose (i - t) : ℚ) * ((i - t : ℕ) : ℚ)
      = ((2 * i - t - 1).choose i : ℚ) * (i : ℚ) := by
    exact_mod_cast congrArg (fun x : ℕ ↦ (x : ℚ)) (choose_mul_sub t i hti)
  have step := mul_le_mul_of_nonneg_right hshadow hitpos.le
  rw [mul_assoc, hcast] at step
  have hQ : ((#(level 𝓕 i) * i : ℕ) : ℚ) * ((2 * i - t - 1).choose i : ℚ)
      ≤ ((#(shadow (i - t) (level 𝓕 i)) * (i - t) : ℕ) : ℚ)
        * ((2 * i - t - 1).choose i : ℚ) := by
    push_cast
    nlinarith [step]
  have hN : #(level 𝓕 i) * i * (2 * i - t - 1).choose i
      ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) * (2 * i - t - 1).choose i := by
    exact_mod_cast hQ
  have key : #(level 𝓕 i) * i ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) :=
    Nat.le_of_mul_le_mul_right hN hNpos
  have hdisjc := shadow_card_add_level_card_le n t i h𝓕 hav hti (by omega)
  calc #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t)
      ≤ #(shadow (i - t) (level 𝓕 i)) * (i - t) + #(level 𝓕 (n + t - i)) * (i - t) := by omega
    _ = (#(shadow (i - t) (level 𝓕 i)) + #(level 𝓕 (n + t - i))) * (i - t) := by ring
    _ ≤ n.choose (i - t) * (i - t) := Nat.mul_le_mul_right _ hdisjc

/-- The paired form of inequality (3): `f_i + f_{n+t-i} ≤ C(n, n + t - i)`. -/
private lemma level_add_level_le (n t i : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hqi : qBound t ≤ i)
    (hi : 2 * i ≤ n + t) :
    #(level 𝓕 i) + #(level 𝓕 (n + t - i)) ≤ n.choose (n + t - i) := by
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hti : t < i := by omega
  have h3 := level_inequality n t i h𝓕 hav ht hqi hi
  have hle : (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t) ≤ n.choose (i - t) * (i - t) := by
    have hstep : (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t)
        ≤ #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) := by
      have : #(level 𝓕 i) * (i - t) ≤ #(level 𝓕 i) * i :=
        Nat.mul_le_mul_left _ (by omega)
      calc (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) * (i - t)
          = #(level 𝓕 i) * (i - t) + #(level 𝓕 (n + t - i)) * (i - t) := by ring
        _ ≤ #(level 𝓕 i) * i + #(level 𝓕 (n + t - i)) * (i - t) := by omega
    omega
  have hfin := Nat.le_of_mul_le_mul_right hle (show 0 < i - t by omega)
  have hch : n.choose (n + t - i) = n.choose (i - t) := by
    rw [show n + t - i = n - (i - t) by omega]
    exact Nat.choose_symm (by omega)
  rw [hch]
  exact hfin

/-- The self-paired middle level when `n + t` is even: `f_{(n+t)/2} ≤ C(n - 1, (n+t)/2)`. -/
private lemma level_middle_le (n t : ℕ) {𝓕 : Finset (Finset ℕ)} (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n)
    (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t) (hq : qBound t ≤ (n + t) / 2)
    (heven : (n + t) % 2 = 0) :
    #(level 𝓕 ((n + t) / 2)) ≤ (n - 1).choose ((n + t) / 2) := by
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  set m := (n + t) / 2 with hmdef
  have hqm : t + 1 ≤ m := by omega
  have hnm : n + t - m = m := by omega
  have hn : 1 ≤ n := by omega
  have h3 := level_inequality n t m h𝓕 hav ht hq (by omega)
  rw [hnm] at h3
  have hkey : #(level 𝓕 m) * n ≤ n.choose (m - t) * (m - t) := by
    have hcomb : #(level 𝓕 m) * m + #(level 𝓕 m) * (m - t) = #(level 𝓕 m) * n := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  have hid : n.choose (m - t) * (m - t) = n * (n - 1).choose m := by
    obtain ⟨k, hk⟩ : ∃ k, m - t = k + 1 := ⟨m - t - 1, by omega⟩
    have hn1 : n - 1 + 1 = n := by omega
    have e : n * (n - 1).choose k = n.choose (k + 1) * (k + 1) := by
      have h := Nat.add_one_mul_choose_eq (n - 1) k
      rw [hn1] at h
      exact h
    have hsym : (n - 1).choose k = (n - 1).choose m := by
      rw [← Nat.choose_symm (show k ≤ n - 1 by omega)]
      congr 1
      omega
    rw [hk, ← e, hsym]
  rw [hid, Nat.mul_comm] at hkey
  exact Nat.le_of_mul_le_mul_left hkey hn

/-- `Ico a (b + 1) = Icc a b`. -/
private lemma Ico_succ_eq_Icc (a b : ℕ) : Finset.Ico a (b + 1) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- `Icc (a + 1) b = Ioc a b`. -/
private lemma Icc_succ_eq_Ioc (a b : ℕ) : Finset.Icc (a + 1) b = Finset.Ioc a b := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- `Ico (a + 1) b = Ioo a b`. -/
private lemma Ico_succ_eq_Ioo (a b : ℕ) : Finset.Ico (a + 1) b = Finset.Ioo a b := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Ioo]
  omega

/-- Reflecting an index range in `N`: `i ↦ N - i` is a bijection `Icc a b → Icc (N - b) (N - a)`. -/
private lemma sum_Icc_reflect (N a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) (g : ℕ → ℕ) :
    ∑ j ∈ Finset.Icc (N - b) (N - a), g j = ∑ i ∈ Finset.Icc a b, g (N - i) := by
  classical
  have hinj : ∀ x ∈ Finset.Icc a b, ∀ y ∈ Finset.Icc a b, N - x = N - y → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    omega
  rw [← Finset.sum_image hinj]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · intro hx
    refine ⟨N - x, ?_, ?_⟩ <;> omega
  · rintro ⟨i, hi, hix⟩
    omega

/-- The level decomposition behind inequality (4): low levels are bounded by binomials, level `t`
is empty, the levels below `qBound t` are kept, the levels in `[qBound t, n + t - qBound t]` are
grouped into the pairs `(i, n + t - i)` (with the self-paired middle level for `n + t` even), and
the top levels are bounded by binomials. -/
private lemma card_le_pair_sum (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ (n + t) / 2) :
    #𝓕 ≤ (∑ i ∈ range t, n.choose i)
        + (∑ i ∈ Finset.Icc (qBound t) (n + t - (n + t) / 2 - 1),
            (#(level 𝓕 i) + #(level 𝓕 (n + t - i))))
        + (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
        + (∑ i ∈ Finset.Ioc (n + t - qBound t) n, n.choose i)
        + ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hmu : m ≤ u := by omega
  have hun : u ≤ n := by omega
  have hcard : #𝓕 = ∑ i ∈ Finset.Ico 0 (n + 1), #(level 𝓕 i) := by
    rw [← Finset.range_eq_Ico]
    simp only [level]
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro A hA
    have h := Finset.card_le_card (h𝓕 A hA)
    rw [Finset.card_range] at h
    exact Finset.mem_range.mpr (by omega)
  have hIco : ∀ a b c : ℕ, a ≤ b → b ≤ c →
      (∑ i ∈ Finset.Ico a b, #(level 𝓕 i)) + (∑ i ∈ Finset.Ico b c, #(level 𝓕 i))
        = ∑ i ∈ Finset.Ico a c, #(level 𝓕 i) :=
    fun a b c hab hbc ↦ Finset.sum_Ico_consecutive _ hab hbc
  have e1 := hIco 0 t (n + 1) (by omega) (by omega)
  have e2 := hIco t (t + 1) (n + 1) (by omega) (by omega)
  have e3 := hIco (t + 1) q (n + 1) (by omega) (by omega)
  have e4 := hIco q (u + 1) (n + 1) (by omega) (by omega)
  have e5 := hIco q (m + 1) (u + 1) (by omega) (by omega)
  have hB1 : ∑ i ∈ Finset.Ico 0 t, #(level 𝓕 i) ≤ ∑ i ∈ range t, n.choose i := by
    rw [Finset.range_eq_Ico]
    exact Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
  have hB2 : ∑ i ∈ Finset.Ico t (t + 1), #(level 𝓕 i) = 0 := by
    rw [Finset.sum_Ico_succ_top (le_refl t), level_eq_empty_of_avoids hav]
    simp
  have hB3 : ∑ i ∈ Finset.Ico (t + 1) q, #(level 𝓕 i)
      = ∑ i ∈ Finset.Ioo t q, #(level 𝓕 i) := by rw [Ico_succ_eq_Ioo]
  have hB6 : ∑ i ∈ Finset.Ico (u + 1) (n + 1), #(level 𝓕 i)
      ≤ ∑ i ∈ Finset.Ioc u n, n.choose i := by
    rw [Ico_succ_eq_Icc, Icc_succ_eq_Ioc]
    exact Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
  have hB4 : ∑ i ∈ Finset.Ico q (m + 1), #(level 𝓕 i)
      = (∑ i ∈ Finset.Icc q m', #(level 𝓕 i))
        + (if (n + t) % 2 = 0 then #(level 𝓕 m) else 0) := by
    split_ifs with hpar
    · have hset : Finset.Ico q m = Finset.Icc q m' := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [Finset.sum_Ico_succ_top (show q ≤ m by omega), hset]
    · have hset : Finset.Ico q (m + 1) = Finset.Icc q m' := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [hset, Nat.add_zero]
  have hB5 : ∑ i ∈ Finset.Ico (m + 1) (u + 1), #(level 𝓕 i)
      = ∑ i ∈ Finset.Icc q m', #(level 𝓕 (n + t - i)) := by
    have hr := sum_Icc_reflect (n + t) q m' (by omega) (by omega) (fun j ↦ #(level 𝓕 j))
    rw [show n + t - m' = m + 1 by omega, ← hudef] at hr
    rw [Ico_succ_eq_Icc]
    exact hr
  have hsum : (∑ i ∈ Finset.Icc q m', #(level 𝓕 i))
      + (∑ i ∈ Finset.Icc q m', #(level 𝓕 (n + t - i)))
      = ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i))) :=
    Finset.sum_add_distrib.symm
  omega

/-- `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} f_i` once `qBound t ≤ (n + t) / 2`. -/
theorem card_le_ffBound_add_middle (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ (n + t) / 2) :
    #𝓕 ≤ ffBound n t + ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have core := card_le_pair_sum n t h𝓕 hav ht hq
  have hmid : (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
      ≤ (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0) := by
    split_ifs with hpar
    · exact level_middle_le n t h𝓕 hav ht hq hpar
    · exact le_refl 0
  rw [ffBound]
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hmu : m ≤ u := by omega
  have hun : u ≤ n := by omega
  have hpair : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      ≤ ∑ i ∈ Finset.Ioc m u, n.choose i := by
    have hb : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
        ≤ ∑ i ∈ Finset.Icc q m', n.choose (n + t - i) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [Finset.mem_Icc] at hi
      exact level_add_level_le n t i h𝓕 hav ht (by omega) (by omega)
    have hr := sum_Icc_reflect (n + t) q m' (by omega) (by omega) (fun j ↦ n.choose j)
    rw [show n + t - m' = m + 1 by omega, ← hudef] at hr
    rw [← Icc_succ_eq_Ioc]
    omega
  have hIocC : (∑ i ∈ Finset.Ioc m u, n.choose i) + (∑ i ∈ Finset.Ioc u n, n.choose i)
      = ∑ i ∈ Finset.Ioc m n, n.choose i := Finset.sum_Ioc_consecutive _ hmu hun
  omega

/-- The refined form of inequality (4) keeping the pair `(n + t - (m + 1), m + 1)`
(`m = (n + t) / 2`) unbounded: its binomial bound `C(n, m + 1)` moves to the left. -/
theorem card_le_ffBound_add_middle_sub (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ n + t - (n + t) / 2 - 1) (hn : (n + t) / 2 + 1 ≤ n) :
    #𝓕 + n.choose ((n + t) / 2 + 1) ≤
      ffBound n t + (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i)) +
        (#(level 𝓕 (n + t - ((n + t) / 2 + 1))) + #(level 𝓕 ((n + t) / 2 + 1))) := by
  classical
  have hqd : qBound t = t + 1 + lcmUpTo t := rfl
  have hq' : qBound t ≤ (n + t) / 2 := by omega
  have core := card_le_pair_sum n t h𝓕 hav ht hq'
  have hmid : (if (n + t) % 2 = 0 then #(level 𝓕 ((n + t) / 2)) else 0)
      ≤ (if (n + t) % 2 = 0 then (n - 1).choose ((n + t) / 2) else 0) := by
    split_ifs with hpar
    · exact level_middle_le n t h𝓕 hav ht hq' hpar
    · exact le_refl 0
  rw [ffBound]
  set q := qBound t with hqdef
  set m := (n + t) / 2 with hmdef
  have hqt : t + 1 ≤ q := by omega
  have htn : t + 2 ≤ n := by omega
  set u := n + t - q with hudef
  set m' := n + t - m - 1 with hm'def
  have hqm' : q ≤ m' := hq
  have hmu : m + 1 ≤ u := by omega
  have hun : u ≤ n := by omega
  rw [show n + t - (m + 1) = m' by omega]
  have hsplitlast : ∑ i ∈ Finset.Icc q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      = (∑ i ∈ Finset.Ico q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i))))
        + (#(level 𝓕 m') + #(level 𝓕 (m + 1))) := by
    rw [← Ico_succ_eq_Icc, Finset.sum_Ico_succ_top hqm', show n + t - m' = m + 1 by omega]
  have hpair : ∑ i ∈ Finset.Ico q m', (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
      ≤ ∑ i ∈ Finset.Ioc (m + 1) u, n.choose i := by
    have hset : Finset.Ico q m' = Finset.Icc q (m' - 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    have hb : ∑ i ∈ Finset.Icc q (m' - 1), (#(level 𝓕 i) + #(level 𝓕 (n + t - i)))
        ≤ ∑ i ∈ Finset.Icc q (m' - 1), n.choose (n + t - i) := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [Finset.mem_Icc] at hi
      exact level_add_level_le n t i h𝓕 hav ht (by omega) (by omega)
    have hr := sum_Icc_reflect (n + t) q (m' - 1) (by omega) (by omega) (fun j ↦ n.choose j)
    rw [show n + t - (m' - 1) = m + 2 by omega, ← hudef,
      show m + 2 = (m + 1) + 1 by omega, Icc_succ_eq_Ioc] at hr
    omega
  have hIocC : (∑ i ∈ Finset.Ioc (m + 1) u, n.choose i) + (∑ i ∈ Finset.Ioc u n, n.choose i)
      = ∑ i ∈ Finset.Ioc (m + 1) n, n.choose i := Finset.sum_Ioc_consecutive _ hmu hun
  have hsingle : Finset.Ioc m (m + 1) = {m + 1} := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have htop : n.choose (m + 1) + (∑ i ∈ Finset.Ioc (m + 1) n, n.choose i)
      = ∑ i ∈ Finset.Ioc m n, n.choose i := by
    have h := Finset.sum_Ioc_consecutive (fun j ↦ n.choose j) (show m ≤ m + 1 by omega) hn
    rw [hsingle, Finset.sum_singleton] at h
    exact h
  omega

/-- The sets `B ⊆ range n` of size `b` with `#(B ∩ A₀) = t` number `C(#A₀, t) · C(n - #A₀, b - t)`
(`A₀ ⊆ range n`, `t ≤ b`), and none of them lies in `𝓕` when `A₀ ∈ 𝓕` and `#A₀ ≠ b`. -/
theorem level_card_le_choose_sub (n t b : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) {A₀ : Finset ℕ}
    (hA₀ : A₀ ∈ 𝓕) (hb : #A₀ ≠ b) (htb : t ≤ b) (htA : t ≤ #A₀) :
    #(level 𝓕 b) + (#A₀).choose t * (n - #A₀).choose (b - t) ≤ n.choose b := by
  classical
  -- `hb` and `htA` are not needed: `hav` forbids `#(B ∩ A₀) = t` even for `B = A₀`.
  have _hb := hb
  have _htA := htA
  have hA₀n : A₀ ⊆ range n := h𝓕 A₀ hA₀
  set 𝓑 : Finset (Finset ℕ) := ((range n).powersetCard b).filter fun B ↦ #(B ∩ A₀) = t with h𝓑
  -- the product injects into `𝓑`
  have hcount : (#A₀).choose t * (n - #A₀).choose (b - t) ≤ #𝓑 := by
    have hcard : #((A₀.powersetCard t) ×ˢ ((range n \ A₀).powersetCard (b - t)))
        = (#A₀).choose t * (n - #A₀).choose (b - t) := by
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hA₀n, Finset.card_range]
    rw [← hcard]
    refine Finset.card_le_card_of_injOn (fun p ↦ p.1 ∪ p.2) ?_ ?_
    · rintro ⟨S, T⟩ hST
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hST
      obtain ⟨⟨hS, hScard⟩, hT, hTcard⟩ := hST
      have hTA : Disjoint T A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT hx)).2 hxA
      have hdisjST : Disjoint S T := Finset.disjoint_of_subset_left hS hTA.symm
      have hinter : (S ∪ T) ∩ A₀ = S := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
          Finset.disjoint_iff_inter_eq_empty.mp hTA, Finset.union_empty]
      simp only [Finset.mem_coe, h𝓑, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.union_subset (hS.trans hA₀n) (hT.trans Finset.sdiff_subset), ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisjST, hScard, hTcard]
        omega
      · rw [hinter, hScard]
    · rintro ⟨S, T⟩ hST ⟨S', T'⟩ hST' heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_powersetCard] at hST hST'
      obtain ⟨⟨hS, -⟩, hT, -⟩ := hST
      obtain ⟨⟨hS', -⟩, hT', -⟩ := hST'
      have hTA : Disjoint T A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT hx)).2 hxA
      have hTA' : Disjoint T' A₀ := by
        rw [Finset.disjoint_left]
        intro x hx hxA
        exact (Finset.mem_sdiff.mp (hT' hx)).2 hxA
      have heq' : S ∪ T = S' ∪ T' := heq
      have hS1 : (S ∪ T) ∩ A₀ = S := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS,
          Finset.disjoint_iff_inter_eq_empty.mp hTA, Finset.union_empty]
      have hS2 : (S' ∪ T') ∩ A₀ = S' := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr hS',
          Finset.disjoint_iff_inter_eq_empty.mp hTA', Finset.union_empty]
      have hSS : S = S' := by rw [← hS1, ← hS2, heq']
      have hT1 : (S ∪ T) \ A₀ = T := by
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hS,
          Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hTA]
      have hT2 : (S' ∪ T') \ A₀ = T' := by
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr hS',
          Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hTA']
      have hTT : T = T' := by rw [← hT1, ← hT2, heq']
      rw [hSS, hTT]
  -- `level 𝓕 b` and `𝓑` are disjoint subsets of the `b`-subsets of `range n`
  have hsub₁ : level 𝓕 b ⊆ (range n).powersetCard b := by
    intro B hB
    rw [mem_level] at hB
    exact Finset.mem_powersetCard.mpr ⟨h𝓕 B hB.1, hB.2⟩
  have hsub₂ : 𝓑 ⊆ (range n).powersetCard b := Finset.filter_subset _ _
  have hdisj : Disjoint (level 𝓕 b) 𝓑 := by
    rw [Finset.disjoint_left]
    intro B hB hB'
    rw [mem_level] at hB
    rw [h𝓑, Finset.mem_filter] at hB'
    exact hav B hB.1 A₀ hA₀ hB'.2
  calc #(level 𝓕 b) + (#A₀).choose t * (n - #A₀).choose (b - t)
      ≤ #(level 𝓕 b) + #𝓑 := by omega
    _ = #(level 𝓕 b ∪ 𝓑) := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #((range n).powersetCard b) := Finset.card_le_card (Finset.union_subset hsub₁ hsub₂)
    _ = n.choose b := by rw [Finset.card_powersetCard, Finset.card_range]

end FranklFuredi

end

/-! ### Upstream module `JSP573/FF/Asymptotics.lean` -/

/-!
# Elementary binomial and growth estimates for the Frankl–Füredi endgame

Leaves used in the final comparison "exponential beats polynomial" of the proof of Theorem 1.3:

* `centralBinom_min_le_choose`: `C(N, k) ≥ C(2j, j)` with `j = min k (N - k)` (repeated Pascal:
  `C(N, k) ≥ C(N - 1, k - 1)` and `C(M, j)` is monotone in `M`);
* `four_pow_le_choose_mul`: `4 ^ j ≤ (2j + 1) · C(2j, j)` (Mathlib's central binomial bound);
* `sum_choose_Ioo_le`: `∑_{t < i < q} C(n, i) ≤ q · n ^ q` for `1 ≤ n`;
* `eventually_mul_pow_lt_two_pow`: for fixed `c, e`, `c · n ^ e < 2 ^ n` for all large `n`.
-/

namespace FranklFuredi

/-- Repeated Pascal: `C(N, k) ≥ C(2j, j)` where `j = min k (N - k)`. -/
theorem centralBinom_min_le_choose (N k : ℕ) (hk : k ≤ N) :
    (2 * min k (N - k)).choose (min k (N - k)) ≤ N.choose k := by
  rcases le_total k (N - k) with h | h
  · rw [min_eq_left h]
    exact Nat.choose_le_choose k (by omega)
  · rw [min_eq_right h]
    calc (2 * (N - k)).choose (N - k) ≤ N.choose (N - k) := Nat.choose_le_choose _ (by omega)
      _ = N.choose k := Nat.choose_symm hk

/-- `4 ^ j ≤ (2j + 1) · C(2j, j)`. -/
theorem four_pow_le_choose_mul (j : ℕ) : 4 ^ j ≤ (2 * j + 1) * (2 * j).choose j :=
  Nat.four_pow_le_two_mul_add_one_mul_central_binom j

/-- `∑_{t < i < q} C(n, i) ≤ q · n ^ q` for `1 ≤ n`. -/
theorem sum_choose_Ioo_le (n t q : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Ioo t q, n.choose i ≤ q * n ^ q := by
  have hbd : ∀ i ∈ Finset.Ioo t q, n.choose i ≤ n ^ q := fun i hi =>
    (Nat.choose_le_pow n i).trans (Nat.pow_le_pow_right hn (le_of_lt (Finset.mem_Ioo.1 hi).2))
  have hcard : (Finset.Ioo t q).card ≤ q := by rw [Nat.card_Ioo]; omega
  calc ∑ i ∈ Finset.Ioo t q, n.choose i ≤ (Finset.Ioo t q).card • n ^ q :=
        Finset.sum_le_card_nsmul _ _ _ hbd
    _ = (Finset.Ioo t q).card * n ^ q := smul_eq_mul _ _
    _ ≤ q * n ^ q := Nat.mul_le_mul_right _ hcard

/-- Polynomials are eventually dominated by `2 ^ n`. -/
theorem eventually_mul_pow_lt_two_pow (c e : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → c * n ^ e < 2 ^ n := by
  have hlim : Filter.Tendsto (fun n : ℕ ↦ (c : ℝ) * ((n : ℝ) ^ e / 2 ^ n)) Filter.atTop
      (nhds 0) := by
    simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 2)).const_mul (c : ℝ)
  obtain ⟨n₀, hn₀⟩ :=
    Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ)))
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have h : (c : ℝ) * ((n : ℝ) ^ e / 2 ^ n) < 1 := hn₀ n hn
  rw [← mul_div_assoc, div_lt_one (by positivity)] at h
  exact_mod_cast h

end FranklFuredi

/-! ### Upstream module `JSP573/FF/Main.lean` -/

section
/-!
# Frankl–Füredi 1984, Theorem 1.3: `T(n, t) = #𝓕*(n, t)` for `n ≥ n₀(t)`

With the level inequalities in place, the proof of the upper bound `#𝓕 ≤ ffBound n t` for a
`t`-avoiding family `𝓕` on `range n` with `n` large runs as follows.

* If `𝓕` has no member of size in `(t, qBound t)`, `card_le_ffBound_add_middle` gives the bound.
* Otherwise pick `A₀ ∈ 𝓕` with `t < a := #A₀ < qBound t`, let `m = (n + t) / 2`, `b = m + 1`
  and `i₀ = n + t - b` (the partner level of `b`; `qBound t ≤ i₀ ≤ m` for `n` large). The level
  `b` omits `M ≥ C(a, t) · C(n - a, b - t) ≥ C(n - a, b - t)` sets (`level_card_le_choose_sub`),
  and the level inequality at `i₀` (note `i₀ - t = n - b`) gives
  `f_{i₀} · i₀ ≤ (C(n, b) - f_b) · (i₀ - t)`, hence
  `f_{i₀} + f_b ≤ C(n, b) - M · t / i₀`. Redoing the summation of `card_le_ffBound_add_middle`
  with this improved pair bound yields
  `#𝓕 ≤ ffBound n t + ∑_{t < i < qBound t} C(n, i) - M · t / i₀`, and for `n ≥ n₀(t)` the
  exponential term `M · t / i₀ ≥ 2^{⌊(n - 2 qBound t)/2⌋ - 1} · t / n` dominates the polynomial
  `∑_{t < i < qBound t} C(n, i) ≤ qBound t · n ^ qBound t`.

The exact value then follows from plby's lower bounds (`franklFurediOdd_card_le_T`,
`franklFurediEven_card_le_T`) and the closed forms `card_franklFurediOdd/Even`.
-/

open _root_.Finset

namespace FranklFuredi

/-- The linear combination closing the endgame: with `i = d + t`, the level inequality
`fi * i + fb * d ≤ C * d`, the deficiency `fb + L ≤ C`, the summation bound
`F + C ≤ E + S + fi + fb` and the domination `i * S ≤ t * L`, one gets `F ≤ E`. -/
private lemma le_of_level_bounds {F E C fb fi S L t d i : ℕ} (hi : i = d + t)
    (h1 : fi * i + fb * d ≤ C * d) (h2 : fb + L ≤ C) (h3 : F + C ≤ E + S + fi + fb)
    (h4 : i * S ≤ t * L) (hpos : 1 ≤ i) : F ≤ E := by
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have m3 : i * (F + C) ≤ i * (E + S + fi + fb) := Nat.mul_le_mul (le_refl i) h3
  have m2 : t * (fb + L) ≤ t * C := Nat.mul_le_mul (le_refl t) h2
  subst hi
  nlinarith [m3, m2, h1, h4]

/-- Exponential beats polynomial: for `n` large the binomial coefficient
`C(n - q, (n + t) / 2 + 1 - t)` dwarfs `n · q · n ^ q`. -/
private lemma mul_pow_le_choose (n t q : ℕ) (ht : 1 ≤ t) (htq : t < q) (hn : 4 * q + 12 ≤ n)
    (hlt : 2 ^ (2 * q + 6) * q * n ^ (q + 2) < 2 ^ n) :
    n * (q * n ^ q) ≤ t * (n - q).choose ((n + t) / 2 + 1 - t) := by
  set k : ℕ := (n + t) / 2 + 1 - t with hkdef
  set N : ℕ := n - q with hNdef
  set j : ℕ := min k (N - k) with hjdef
  have hkN : k ≤ N := by omega
  have hcb : (2 * j).choose j ≤ N.choose k := by
    rw [hjdef]
    exact centralBinom_min_le_choose N k hkN
  have h4j : 4 ^ j ≤ (2 * j + 1) * N.choose k :=
    (four_pow_le_choose_mul j).trans (Nat.mul_le_mul (le_refl (2 * j + 1)) hcb)
  have hpow : 2 ^ (n - 2 * q - 5) ≤ 4 ^ j := by
    have h1 : n - 2 * q - 5 ≤ 2 * j := by omega
    calc 2 ^ (n - 2 * q - 5) ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) h1
      _ = 4 ^ j := by rw [pow_mul]; norm_num
  have hkey : 2 * (q * n ^ (q + 2)) < 2 ^ (n - 2 * q - 5) := by
    have hsplit : (2 : ℕ) ^ n = 2 ^ (2 * q + 5) * 2 ^ (n - 2 * q - 5) := by
      rw [← pow_add]
      congr 1
      omega
    have heq : 2 ^ (2 * q + 6) * q * n ^ (q + 2)
        = 2 ^ (2 * q + 5) * (2 * (q * n ^ (q + 2))) := by
      have h26 : (2 : ℕ) ^ (2 * q + 6) = 2 ^ (2 * q + 5) * 2 := by ring
      rw [h26]
      ring
    rw [hsplit, heq] at hlt
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hLbound : 2 * n * (n * (q * n ^ q)) < 2 * n * N.choose k := by
    calc 2 * n * (n * (q * n ^ q)) = 2 * (q * n ^ (q + 2)) := by ring
      _ < 2 ^ (n - 2 * q - 5) := hkey
      _ ≤ 4 ^ j := hpow
      _ ≤ (2 * j + 1) * N.choose k := h4j
      _ ≤ 2 * n * N.choose k := Nat.mul_le_mul (by omega) (le_refl (N.choose k))
  have hfinal : n * (q * n ^ q) < N.choose k := Nat.lt_of_mul_lt_mul_left hLbound
  calc n * (q * n ^ q) ≤ N.choose k := le_of_lt hfinal
    _ ≤ t * N.choose k := Nat.le_mul_of_pos_left _ ht

/-- The upper bound `#𝓕 ≤ ffBound n t` under the three numeric side conditions on `n`. -/
private lemma card_le_ffBound_of_numeric (n t : ℕ) {𝓕 : Finset (Finset ℕ)}
    (h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n) (hav : Erdos703.AvoidsRIntersection t 𝓕) (ht : 1 ≤ t)
    (hq : qBound t ≤ n + t - (n + t) / 2 - 1) (hn : (n + t) / 2 + 1 ≤ n)
    (hbig : n * (qBound t * n ^ qBound t) ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t)) :
    #𝓕 ≤ ffBound n t := by
  classical
  have htq : t < qBound t := by
    have h : qBound t = t + 1 + lcmUpTo t := rfl
    omega
  by_cases hemp : ∀ i ∈ Finset.Ioo t (qBound t), level 𝓕 i = ∅
  · have hzero : ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) = 0 :=
      Finset.sum_eq_zero fun i hi ↦ by rw [hemp i hi, Finset.card_empty]
    have h := card_le_ffBound_add_middle n t h𝓕 hav ht (by omega)
    rw [hzero] at h
    omega
  · push Not at hemp
    obtain ⟨a, ha, hane⟩ := hemp
    rw [Finset.mem_Ioo] at ha
    obtain ⟨A₀, hA₀⟩ := hane
    rw [mem_level] at hA₀
    obtain ⟨hA₀mem, hA₀card⟩ := hA₀
    have hn1 : 1 ≤ n := by omega
    have hS : ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i) ≤ qBound t * n ^ qBound t := by
      calc ∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i)
          ≤ ∑ i ∈ Finset.Ioo t (qBound t), n.choose i :=
            Finset.sum_le_sum fun i _ ↦ level_card_le_choose n i h𝓕
        _ ≤ qBound t * n ^ qBound t := sum_choose_Ioo_le n t (qBound t) hn1
    have hbne : #A₀ ≠ (n + t) / 2 + 1 := by omega
    have htb : t ≤ (n + t) / 2 + 1 := by omega
    have htA : t ≤ #A₀ := by omega
    have hsub := level_card_le_choose_sub n t ((n + t) / 2 + 1) h𝓕 hav hA₀mem hbne htb htA
    have hL : (n - qBound t).choose ((n + t) / 2 + 1 - t)
        ≤ (#A₀).choose t * (n - #A₀).choose ((n + t) / 2 + 1 - t) := by
      have h1 : 1 ≤ (#A₀).choose t := Nat.choose_pos (by omega)
      have h2 : (n - qBound t).choose ((n + t) / 2 + 1 - t)
          ≤ (n - #A₀).choose ((n + t) / 2 + 1 - t) := Nat.choose_le_choose _ (by omega)
      calc (n - qBound t).choose ((n + t) / 2 + 1 - t)
          = 1 * (n - qBound t).choose ((n + t) / 2 + 1 - t) := (one_mul _).symm
        _ ≤ (#A₀).choose t * (n - #A₀).choose ((n + t) / 2 + 1 - t) := Nat.mul_le_mul h1 h2
    have h2 : #(level 𝓕 ((n + t) / 2 + 1)) + (n - qBound t).choose ((n + t) / 2 + 1 - t)
        ≤ n.choose ((n + t) / 2 + 1) := by omega
    have hlev := level_inequality n t (n + t - ((n + t) / 2 + 1)) h𝓕 hav ht (by omega) (by omega)
    have he1 : n + t - (n + t - ((n + t) / 2 + 1)) = (n + t) / 2 + 1 := by omega
    have he2 : n + t - ((n + t) / 2 + 1) - t = n - ((n + t) / 2 + 1) := by omega
    rw [he1, he2, Nat.choose_symm hn] at hlev
    have hmain := card_le_ffBound_add_middle_sub n t h𝓕 hav ht hq hn
    have h4 : (n + t - ((n + t) / 2 + 1)) * (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i))
        ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t) :=
      le_trans (Nat.mul_le_mul (by omega) hS) hbig
    have hid : n + t - ((n + t) / 2 + 1) = n - ((n + t) / 2 + 1) + t := by omega
    have h3 : #𝓕 + n.choose ((n + t) / 2 + 1)
        ≤ ffBound n t + (∑ i ∈ Finset.Ioo t (qBound t), #(level 𝓕 i))
          + #(level 𝓕 (n + t - ((n + t) / 2 + 1))) + #(level 𝓕 ((n + t) / 2 + 1)) := by omega
    have hposi : 1 ≤ n + t - ((n + t) / 2 + 1) := by omega
    exact le_of_level_bounds hid hlev h2 h3 h4 hposi

/-- The upper bound of Theorem 1.3, for all sufficiently large `n`. -/
theorem exists_upper_bound (t : ℕ) (ht : 1 ≤ t) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ 𝓕 : Finset (Finset ℕ), 𝓕 ⊆ (range n).powerset → Erdos703.AvoidsRIntersection t 𝓕 →
      #𝓕 ≤ ffBound n t := by
  have htq : t < qBound t := by
    have h : qBound t = t + 1 + lcmUpTo t := rfl
    omega
  obtain ⟨n₁, hn₁⟩ :=
    eventually_mul_pow_lt_two_pow (2 ^ (2 * qBound t + 6) * qBound t) (qBound t + 2)
  refine ⟨max n₁ (4 * qBound t + 12), fun n hn 𝓕 hsub hav ↦ ?_⟩
  have hnb : 4 * qBound t + 12 ≤ n := le_trans (le_max_right _ _) hn
  have h𝓕 : ∀ A ∈ 𝓕, A ⊆ range n := fun A hA ↦ Finset.mem_powerset.mp (hsub hA)
  have hbig : n * (qBound t * n ^ qBound t)
      ≤ t * (n - qBound t).choose ((n + t) / 2 + 1 - t) :=
    mul_pow_le_choose n t (qBound t) ht htq hnb (hn₁ n (le_trans (le_max_left _ _) hn))
  exact card_le_ffBound_of_numeric n t h𝓕 hav ht (by omega) (by omega) hbig

/-- Theorem 1.3 (Frankl–Füredi 1984): for every `t ≥ 1` and all sufficiently large `n`,
`T(n, t) = #𝓕*(n, t) = ffBound n t`. -/
theorem frankl_furedi (t : ℕ) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Erdos703.T n t = ffBound n t := by
  obtain ⟨n₀, hn₀⟩ := exists_upper_bound t ht
  refine ⟨max n₀ 1, fun n hn ↦ le_antisymm ?_ ?_⟩
  · exact Erdos703.T_le_of_forall (hn₀ n (le_trans (le_max_left _ _) hn))
  · have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    by_cases hpar : (n + t) % 2 = 0
    · rw [← card_franklFurediEven n t hn1 hpar]
      exact Erdos703.franklFurediEven_card_le_T n t hn1 hpar
    · rw [← card_franklFurediOdd n t (by omega)]
      exact Erdos703.franklFurediOdd_card_le_T n t

/-- Together with `T(n, 0) = 2 ^ (n - 1)` (Erdős's trivial case, plby), the exact value is known
for every `r` and all large `n`. -/
theorem erdos_703_exact (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      Erdos703.T n r = if r = 0 then 2 ^ (n - 1) else ffBound n r := by
  by_cases hr : r = 0
  · subst hr
    refine ⟨1, fun n hn ↦ ?_⟩
    rw [Erdos703.T_zero n hn]
    simp
  · obtain ⟨n₀, hn₀⟩ := frankl_furedi r (Nat.one_le_iff_ne_zero.mpr hr)
    refine ⟨n₀, fun n hn ↦ ?_⟩
    rw [hn₀ n hn]
    simp [hr]

end FranklFuredi

end

/-- Erdős Problem 703: the Frankl--Rödl exponential gap in the linear range, and the
Frankl--Füredi exact value of `T n r` for each fixed `r` and all sufficiently large `n`. -/
theorem erdos_703 :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n r : ℕ), ε * n < r → r < (1 / 2 - ε) * n → (T n r : ℝ) < (2 - δ) ^ n) ∧
    (∀ r : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      T n r = if r = 0 then 2 ^ (n - 1) else FranklFuredi.ffBound n r) :=
  ⟨erdos_703_gap, FranklFuredi.erdos_703_exact⟩

#print axioms erdos_703
-- 'Erdos703.erdos_703' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos703
