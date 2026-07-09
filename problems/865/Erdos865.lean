import Mathlib

namespace Erdos865

-- ============================================================
-- Defs
-- ============================================================

open scoped BigOperators
open Finset

/-- `A` contains a *pairwise-sum triple*: distinct `a, b, c ∈ A` with
`a+b, a+c, b+c ∈ A`. -/
def HasTriple (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- `A` is *triple-free* if it contains no pairwise-sum triple. -/
def IsTripleFree (A : Finset ℕ) : Prop := ¬ HasTriple A

/-! ### Folded additive lemma definitions -/

/-- Non-wrapped pair sums `x + y` (`x ≠ y`, both in `B`, `x + y < m`). -/
def lowSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  ((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ p.1 + p.2 < m)).image (fun p => p.1 + p.2)

/-- Wrapped pair sums `x + y - m` (`x ≠ y`, both in `B`, `x + y > m`). -/
def highSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  ((B ×ˢ B).filter (fun p => p.1 ≠ p.2 ∧ m < p.1 + p.2)).image (fun p => p.1 + p.2 - m)

/-- Residues arising both as a non-wrapped and as a wrapped pair sum. -/
def collisions (m : ℕ) (B : Finset ℕ) : Finset ℕ := lowSums m B ∩ highSums m B

/-- The hypothesis `(1.1)` of the folded additive lemma: `B ⊆ {1,…,m-1}` and for
all distinct `x, y ∈ B`, `x + y ≠ m` and the residue of `x + y` mod `m` is not in
`B`. -/
def FoldedOK (m : ℕ) (B : Finset ℕ) : Prop :=
  (∀ b ∈ B, 1 ≤ b ∧ b < m) ∧
  (∀ x ∈ B, ∀ y ∈ B, x ≠ y → x + y ≠ m ∧ (x + y) % m ∉ B)

/-! ### Folding definitions -/

/-- `X = {r : 1 ≤ r < h, r ∈ A}`. -/
def Xset (A : Finset ℕ) (h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => r ∈ A)

/-- `Y = {r : 1 ≤ r < h, h + r ≤ N, h + r ∈ A}`. -/
def Yset (A : Finset ℕ) (N h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => h + r ≤ N ∧ h + r ∈ A)

/-- `B_h = X ∩ Y`. -/
def Bset (A : Finset ℕ) (N h : ℕ) : Finset ℕ := Xset A h ∩ Yset A N h

/-- `E = [1, h-1] \ (X ∪ Y)`. -/
def Eset (A : Finset ℕ) (N h : ℕ) : Finset ℕ :=
  (Finset.Ico 1 h) \ (Xset A h ∪ Yset A N h)

-- ============================================================
-- FoldedAux
-- ============================================================

open scoped BigOperators
open Finset

/-! ### Generic helpers -/

/-
Inclusion–exclusion upper bound for four finite sets.
-/
theorem four_card_le {X : Type*} [DecidableEq X] (s1 s2 s3 s4 : Finset X) :
    s1.card + s2.card + s3.card + s4.card ≤
      (s1 ∪ s2 ∪ s3 ∪ s4).card +
        ((s1 ∩ s2).card + (s1 ∩ s3).card + (s1 ∩ s4).card +
          (s2 ∩ s3).card + (s2 ∩ s4).card + (s3 ∩ s4).card) := by
  have h1 := Finset.card_union_add_card_inter s1 ( s2 ∪ s3 ∪ s4 );
  have h2 := Finset.card_union_add_card_inter s2 ( s3 ∪ s4 ) ; ( have h3 := Finset.card_union_add_card_inter s3 s4; ( simp_all +decide [ Finset.inter_union_distrib_left ] ) );
  linarith [ Finset.card_union_add_card_inter ( s1 ∩ s2 ) ( s1 ∩ s3 ∪ s1 ∩ s4 ), Finset.card_union_add_card_inter ( s1 ∩ s3 ) ( s1 ∩ s4 ), Finset.card_union_add_card_inter ( s2 ∩ s3 ) ( s2 ∩ s4 ) ]

/-
In `ZMod m` the equation `2 * x = c` has at most two solutions.
-/
theorem card_two_sol (m : ℕ) [NeZero m] (c : ZMod m) :
    (Finset.univ.filter (fun x : ZMod m => 2 * x = c)).card ≤ 2 := by
  by_contra! h_contra;
  -- Let S = univ.filter (fun x : ZMod m => 2*x = c). Show S ⊆ {a, b} where a = ((c.val/2 : ℕ) : ZMod m) and b = (((c.val+m)/2 : ℕ) : ZMod m); then card S ≤ card {a,b} ≤ 2 (Finset.card_le_card and Finset.card_le_two, or card_insert_le / card_pair).
  obtain ⟨a, b, hab⟩ : ∃ a b : ZMod m, ∀ x : ZMod m, 2 * x = c → x = a ∨ x = b := by
    use ((c.val / 2 : ℕ) : ZMod m), (((c.val + m) / 2 : ℕ) : ZMod m);
    intro x hx
    have h_eq : (2 * x.val : ℕ) % m = c.val % m := by
      simp +decide [ ← ZMod.natCast_eq_natCast_iff', hx ];
    -- Since $2 * x.val \equiv c.val \pmod{m}$, we have $2 * x.val = c.val + k * m$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * x.val = c.val + k * m := by
      exact ⟨ ( 2 * x.val ) / m, by linarith [ Nat.mod_add_div ( 2 * x.val ) m, Nat.mod_eq_of_lt ( show c.val < m from ZMod.val_lt c ) ] ⟩;
    rcases k with ( _ | _ | k ) <;> norm_num at *;
    · norm_num [ ← hk, mul_comm ];
    · norm_num [ ← hk, Nat.add_div ];
    · nlinarith [ x.val_lt, c.val_lt ];
  exact h_contra.not_ge ( le_trans ( Finset.card_le_card ( show Finset.filter ( fun x : ZMod m => 2 * x = c ) Finset.univ ⊆ { a, b } by intros x hx; aesop ) ) ( Finset.card_insert_le _ _ ) )

/-! ### The four sets `T₁,…,T₄` in `ZMod m` -/

/-- `T₁ = B` inside `ZMod m`. -/
def T1 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) := B.image (fun b : ℕ => (b : ZMod m))

/-- `T₂ = -B` inside `ZMod m`. -/
def T2 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) := B.image (fun b : ℕ => -(b : ZMod m))

/-- `T₃ = (B - α) \ {0}` inside `ZMod m`. -/
def T3 (m : ℕ) (B : Finset ℕ) (α : ℕ) : Finset (ZMod m) :=
  (B.image (fun b : ℕ => (b : ZMod m) - (α : ZMod m))).erase 0

/-- `T₄ = (β - B) \ {0}` inside `ZMod m`. -/
def T4 (m : ℕ) (B : Finset ℕ) (β : ℕ) : Finset (ZMod m) :=
  (B.image (fun b : ℕ => (β : ZMod m) - (b : ZMod m))).erase 0

/-
The cast `ℕ → ZMod m` is injective on `B` when `B ⊆ {1,…,m-1}`.
-/
theorem cast_injOn {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) :
    Set.InjOn (fun b : ℕ => (b : ZMod m)) (B : Set ℕ) := by
  intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

theorem card_T1 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (T1 m B).card = B.card := by
  exact Finset.card_image_of_injOn (cast_injOn hB)

theorem card_T2 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (T2 m B).card = B.card := by
  apply Finset.card_image_of_injOn;
  intro x hx y hy; have := cast_injOn hB; aesop;

theorem card_T3 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B) :
    (T3 m B α).card = B.card - 1 := by
  rw [ Erdos865.T3, Finset.card_erase_of_mem ];
  · rw [ Finset.card_image_of_injOn ];
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ by simpa [ ZMod.natCast_eq_natCast_iff' ] using h;
  · aesop

theorem card_T4 {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ} (hβ : β ∈ B) :
    (T4 m B β).card = B.card - 1 := by
  have h_inj : Set.InjOn (fun b : ℕ => (β : ZMod m) - (b : ZMod m)) (B : Set ℕ) := by
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
    exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h;
  convert Finset.card_erase_of_mem _;
  · grind +splitIndPred;
  · aesop

/-
None of the four sets contain `0`, so their union misses `0`.
-/
theorem union_card_le {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) (α β : ℕ) :
    haveI : NeZero m := ⟨by omega⟩
    (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card ≤ m - 1 := by
  convert Finset.card_le_card _;
  convert rfl;
  convert Finset.card_erase_of_mem ( Finset.mem_univ ( 0 : ZMod m ) );
  convert rfl;
  convert ZMod.card m;
  cases m <;> [ tauto; exact inferInstance ];
  intro x hx; simp_all +decide [ Finset.subset_iff ] ;
  rcases hx with ( hx | hx | hx | hx ) <;> simp_all +decide [ T1, T2, T3, T4 ];
  · rcases hx with ⟨ a, ha, rfl ⟩ ; have := hB.1 a ha; rcases this with ⟨ _, _ ⟩ ; rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
    exact Nat.not_dvd_of_pos_of_lt ‹_› ( by linarith );
  · rcases hx with ⟨ a, ha, rfl ⟩ ; have := hB.1 a ha; rcases this with ⟨ _, _ ⟩ ; rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod ] ;
    exact Nat.not_dvd_of_pos_of_lt ‹_› ( by linarith )

/-! ### The pairwise intersection bounds -/

theorem inter_T1_T2_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) :
    (T1 m B ∩ T2 m B).card ≤ 1 := by
  -- Take an arbitrary element z ∈ T1 m B ∩ T2 m B.
  have h_eq : ∀ z ∈ T1 m B ∩ T2 m B, ∃ b ∈ B, z = (b : ZMod m) ∧ 2 * b = m := by
    intro z hz
    obtain ⟨b, hbB, hbz⟩ : ∃ b ∈ B, (b : ZMod m) = z := by
      unfold T1 at hz; aesop;
    obtain ⟨b', hb'B, hb'z⟩ : ∃ b' ∈ B, -(b' : ZMod m) = z := by
      unfold T2 at hz; aesop;
    have h_eq : m ∣ (b + b') := by
      simp_all +decide [ ← ZMod.natCast_eq_zero_iff ];
      rw [ ← hb'z, neg_add_cancel ];
    have h_eq : b + b' = m := by
      have := hB.1 b hbB; have := hB.1 b' hb'B; obtain ⟨ k, hk ⟩ := h_eq; nlinarith [ show k = 1 by nlinarith ] ;
    have := hB.2 b hbB b' hb'B; simp_all +decide [ two_mul ] ;
    grind;
  exact Finset.card_le_one.mpr fun x hx y hy => by obtain ⟨ b₁, hb₁, rfl, hb₁' ⟩ := h_eq x hx; obtain ⟨ b₂, hb₂, rfl, hb₂' ⟩ := h_eq y hy; aesop;

theorem inter_T1_T2_odd {m : ℕ} (hodd : ¬ 2 ∣ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    T1 m B ∩ T2 m B = ∅ := by
  simp +decide [ T1, T2, Finset.ext_iff ] at *;
  intro a ha b hb; rw [ neg_eq_iff_add_eq_zero ] ; have := hB.1 a ha; have := hB.1 b hb; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
  by_contra h_contra
  have h_div : m ∣ (a + b) := by
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff, add_comm ]
  have h_eq : a + b = m := by
    obtain ⟨ k, hk ⟩ := h_div; nlinarith [ show k = 1 by nlinarith ] ;
  have h_contra' : a ≠ b := by
    omega
  have h_contra'' : a + b ≠ m := by
    exact hB.2 a ha b hb h_contra' |>.1
  contradiction

theorem inter_T1_T3_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B) :
    (T1 m B ∩ T3 m B α).card ≤ 1 := by
  by_contra h_contra;
  obtain ⟨x, hx⟩ : ∃ x ∈ T1 m B ∩ T3 m B α, x ≠ (α : ZMod m) := by
    exact Exists.elim ( Finset.exists_mem_ne ( lt_of_not_ge h_contra ) _ ) fun x hx => ⟨ x, hx.1, hx.2 ⟩;
  obtain ⟨b, hb, hb_eq⟩ : ∃ b ∈ B, x = (b : ZMod m) := by
    unfold T1 at hx; aesop;
  obtain ⟨c, hc, hc_eq⟩ : ∃ c ∈ B, x = (c : ZMod m) - (α : ZMod m) ∧ c ≠ α := by
    unfold T3 at hx; aesop;
  have h_mod : (b + α) % m = c % m := by
    simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
    linear_combination' -hb_eq;
  have := hB.2 b hb α hα; simp_all +decide [ Nat.mod_eq_of_lt ] ;
  exact this ( by aesop ) |>.2 ( by simpa [ Nat.mod_eq_of_lt ( show c < m from hB.1 c hc |>.2 ) ] using hc )

theorem inter_T2_T3_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α : ℕ} (hα : α ∈ B)
    (hmin : ∀ x ∈ B, α ≤ x) : (T2 m B ∩ T3 m B α).card ≤ 1 := by
  -- Since $z \in T2 \cap T3$, we have $z = -(u : ZMod m)$ and $u \in B$, and $z = (b : ZMod m) - (α : ZMod m)$ and $b \in B$. Thus,
  have h_eq : ∀ z ∈ T2 m B ∩ T3 m B α, ∃ u ∈ B, z = -(u : ZMod m) ∧ ∃ b ∈ B, z = (b : ZMod m) - (α : ZMod m) ∧ u = b ∧ 2 * u = α + m := by
    intro z hz
    obtain ⟨u, huB, hu⟩ : ∃ u ∈ B, z = -(u : ZMod m) := by
      unfold T2 at hz; aesop;
    obtain ⟨b, hbB, hb⟩ : ∃ b ∈ B, z = (b : ZMod m) - (α : ZMod m) := by
      rw [Finset.mem_inter] at hz
      obtain ⟨_, hz3⟩ := hz
      simp only [T3, Finset.mem_erase, Finset.mem_image] at hz3
      obtain ⟨_, b, hb, hbeq⟩ := hz3
      exact ⟨b, hb, hbeq.symm⟩
    have h_eq : (u + b : ℕ) % m = α % m := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      linear_combination' hu
    have h_eq' : (u + b : ℕ) = α ∨ (u + b : ℕ) = α + m := by
      have h_eq' : (u + b : ℕ) < 2 * m := by
        linarith [ hB.1 u huB, hB.1 b hbB ];
      have h_eq' : (u + b : ℕ) = α + m * ((u + b) / m) := by
        linarith [ Nat.mod_add_div ( u + b ) m, Nat.mod_eq_of_lt ( show α < m from hB.1 α hα |>.2 ) ];
      have : ( u + b ) / m ≤ 1 := Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by linarith ) ; interval_cases ( u + b ) / m <;> simp +decide at h_eq' ⊢;
      · exact Or.inl h_eq';
      · exact Or.inr h_eq'
    have h_eq'' : u = b := by
      cases h_eq' <;> have := hB.2 u huB b hbB <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · grind +qlia;
      · have := hB.1 α hα; simp_all +decide [ Nat.mod_eq_of_lt ] ;
    have h_eq''' : 2 * u = α + m := by
      cases h_eq' <;> simp_all +decide [ two_mul ];
      linarith [ hmin _ hbB, show α > 0 from hB.1 _ hα |>.1 ]
    use u, huB, hu, b, hbB, hb, h_eq'', h_eq''';
  -- Since $2u = α + m$, and $u$ is uniquely determined, the set $T2 \cap T3$ can contain at most one element.
  have h_unique : ∀ z ∈ T2 m B ∩ T3 m B α, ∀ z' ∈ T2 m B ∩ T3 m B α, z = z' := by
    grind;
  exact Finset.card_le_one.mpr h_unique

theorem inter_T2_T4_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ} (hβ : β ∈ B) :
    (T2 m B ∩ T4 m B β).card ≤ 1 := by
  rw [ Finset.card_le_one_iff ];
  intros a b ha hb
  have h_eq : ∀ z ∈ T2 m B ∩ T4 m B β, z = -(β : ZMod m) := by
    intros z hz
    obtain ⟨u, hu⟩ : ∃ u ∈ B, z = -(u : ZMod m) := by
      unfold T2 at hz; aesop;
    obtain ⟨b, hb⟩ : ∃ b ∈ B, z = (β : ZMod m) - (b : ZMod m) := by
      unfold T4 at hz; aesop;
    have h_eq : (b : ZMod m) = (β : ZMod m) + (u : ZMod m) := by
      grind;
    have h_eq_mod : (β + u) % m = b % m := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
    have h_eq_mod : (β + u) % m ∈ B := by
      have := hB.1 b hb.1; simp_all +decide [ Nat.mod_eq_of_lt ] ;
    have := hB.2 β hβ u hu.1; simp_all +decide [ Nat.mod_eq_of_lt ] ;
  rw [ h_eq a ha, h_eq b hb ]

theorem inter_T1_T4_le {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {β : ℕ}
    (hβ : β ∈ B) : (T1 m B ∩ T4 m B β).card ≤ 2 := by
  have := @card_two_sol m ?_ ( β : ZMod m );
  refine le_trans ( Finset.card_le_card ?_ ) this;
  all_goals try exact ⟨ by linarith ⟩;
  intro x hx; simp_all +decide [ T1, T4 ] ;
  obtain ⟨ ⟨ a, ha, rfl ⟩, hx, ⟨ b, hb, hx' ⟩ ⟩ := hx; simp_all +decide [ sub_eq_iff_eq_add ] ;
  by_cases hab : a = b <;> simp_all +decide [ two_mul ];
  have := hB.2 a ha b hb hab; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  have := hB.1 β hβ; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
  have := Nat.mod_eq_of_lt this.2; simp_all +decide [ ← ZMod.val_natCast ] ;

set_option maxHeartbeats 1000000 in
theorem inter_T3_T4_le {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) {α β : ℕ}
    (hα : α ∈ B) (hβ : β ∈ B) (hαβ : α < β) (hmin : ∀ x ∈ B, α ≤ x)
    (hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x) (hsum : α + β < m)
    (hnc : α + β ∉ collisions m B) : (T3 m B α ∩ T4 m B β).card ≤ 2 := by
  have h_inter_T3_T4_le : ∀ z ∈ T3 m B α ∩ T4 m B β, ∀ b ∈ B, ∀ b' ∈ B, z = (b : ZMod m) - (α : ZMod m) ∧ z = (β : ZMod m) - (b' : ZMod m) → b = β ∨ ∃ c ∈ B, 2 * c = α + β + m ∧ z = (c : ZMod m) - (α : ZMod m) := by
    intros z hz b hb b' hb' h_eq
    have h_sum : (b + b') % m = (α + β) % m := by
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      grind
    have h_cases : b + b' = α + β ∨ b + b' = α + β + m := by
      obtain ⟨ k, hk ⟩ := Nat.modEq_iff_dvd.mp h_sum.symm;
      rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> norm_num at hk ⊢ <;> first | left; nlinarith [ hB.1 b hb, hB.1 b' hb' ] | skip;
      exact Or.inr ( by nlinarith [ show k = 1 by nlinarith [ hB.1 b hb, hB.1 b' hb' ] ] )
    cases' h_cases with h_case1 h_case2
    generalize_proofs at *; (
    by_cases hb_eq_α : b = α <;> by_cases hb'_eq_β : b' = β <;> simp_all +decide [ add_comm ] ;
    · unfold T3 T4 at hz; aesop;
    · omega;
    · grind +splitImp);
    by_cases hbb' : b = b' <;> simp_all +decide [ collisions ];
    · exact Or.inr ⟨ b', hb', by linarith, rfl ⟩;
    · contrapose! hnc; simp_all +decide [ lowSums, highSums ] ;
      exact ⟨ ⟨ α, β, ⟨ ⟨ hα, hβ ⟩, by linarith, by linarith ⟩, rfl ⟩, ⟨ b, b', ⟨ ⟨ hb, hb' ⟩, hbb', by linarith ⟩, Nat.sub_eq_of_eq_add <| by linarith ⟩ ⟩;
  have h_inter_T3_T4_le : ∀ z ∈ T3 m B α ∩ T4 m B β, z = (β : ZMod m) - (α : ZMod m) ∨ ∃ c ∈ B, 2 * c = α + β + m ∧ z = (c : ZMod m) - (α : ZMod m) := by
    intro z hz
    have hz3 : z ∈ T3 m B α := (Finset.mem_inter.mp hz).1
    have hz4 : z ∈ T4 m B β := (Finset.mem_inter.mp hz).2
    simp only [T3, Finset.mem_erase, Finset.mem_image] at hz3
    simp only [T4, Finset.mem_erase, Finset.mem_image] at hz4
    obtain ⟨_, b, hb, hbeq⟩ := hz3
    obtain ⟨_, b', hb', hbeq'⟩ := hz4
    rcases h_inter_T3_T4_le z hz b hb b' hb' ⟨hbeq.symm, hbeq'.symm⟩ with hb_eq | ⟨c, hc, hceq, hzeq⟩
    · left; rw [← hbeq, hb_eq]
    · right; exact ⟨c, hc, hceq, hzeq⟩
  have h_inter_T3_T4_le : ∀ c1 c2 : ℕ, c1 ∈ B → c2 ∈ B → 2 * c1 = α + β + m → 2 * c2 = α + β + m → c1 = c2 := by
    intros c1 c2 hc1 hc2 hc1_eq hc2_eq
    linarith;
  have h_inter_T3_T4_le : ∀ z1 z2 : ZMod m, z1 ∈ T3 m B α ∩ T4 m B β → z2 ∈ T3 m B α ∩ T4 m B β → z1 = (β : ZMod m) - (α : ZMod m) ∨ z2 = (β : ZMod m) - (α : ZMod m) ∨ z1 = z2 := by
    grind;
  contrapose! h_inter_T3_T4_le;
  obtain ⟨ z1, hz1, z2, hz2, hne ⟩ := Finset.two_lt_card.mp h_inter_T3_T4_le;
  grind

/-! ### The Case 2 bound -/

/-
The four-set union bound of Case 2 of the folded additive lemma.
-/
theorem case2_bound {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {α β : ℕ}
    (hα : α ∈ B) (hβ : β ∈ B) (hαβ : α < β) (hmin : ∀ x ∈ B, α ≤ x)
    (hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x) (hsum : α + β < m)
    (hnc : α + β ∉ collisions m B) : 4 * B.card ≤ m + 8 := by
  by_cases h_even : 2 ∣ m;
  · have := ( four_card_le ( T1 m B ) ( T2 m B ) ( T3 m B α ) ( T4 m B β ) );
    rw [ card_T1 hB, card_T2 hB, card_T3 hB hα, card_T4 hB hβ ] at this;
    have := union_card_le hm hB α β;
    have := inter_T1_T2_le hB; ( have := inter_T1_T3_le hB hα; ( have := inter_T1_T4_le hm hB hβ; ( have := inter_T2_T3_le hB hα hmin; ( have := inter_T2_T4_le hB hβ; ( have := inter_T3_T4_le hB hα hβ hαβ hmin hmin2 hsum hnc; omega; ) ) ) ) );
  · have h_union_card : (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card ≤ m - 1 := by
      convert union_card_le hm hB α β using 1;
    have h_four_card_le : (T1 m B).card + (T2 m B).card + (T3 m B α).card + (T4 m B β).card ≤ (T1 m B ∪ T2 m B ∪ T3 m B α ∪ T4 m B β).card + ((T1 m B ∩ T2 m B).card + (T1 m B ∩ T3 m B α).card + (T1 m B ∩ T4 m B β).card + (T2 m B ∩ T3 m B α).card + (T2 m B ∩ T4 m B β).card + (T3 m B α ∩ T4 m B β).card) := by
      convert four_card_le ( T1 m B ) ( T2 m B ) ( T3 m B α ) ( T4 m B β ) using 1;
    have := inter_T1_T3_le hB hα; have := inter_T2_T3_le hB hα hmin; have := inter_T2_T4_le hB hβ; have := inter_T1_T4_le hm hB hβ; have := inter_T3_T4_le hB hα hβ hαβ hmin hmin2 hsum hnc; simp_all +decide [ card_T1, card_T2, card_T3, card_T4 ] ;
    have := inter_T1_T2_odd ( show ¬2 ∣ m from by omega ) hB; simp_all +decide [ Finset.ext_iff ] ; omega;

-- ============================================================
-- FoldedMain
-- ============================================================

open scoped BigOperators
open Finset

/-! ### Monotonicity of the sum sets -/

theorem foldedOK_subset {m : ℕ} {B C : Finset ℕ} (hB : FoldedOK m B) (h : C ⊆ B) :
    FoldedOK m C := by
  constructor;
  · exact fun x hx => hB.1 x ( h hx );
  · exact fun x hx y hy hxy => ⟨ hB.2 x ( h hx ) y ( h hy ) hxy |>.1, fun hxy' => hB.2 x ( h hx ) y ( h hy ) hxy |>.2 <| h hxy' ⟩

theorem lowSums_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) : lowSums m B ⊆ lowSums m C := by
  exact Finset.image_subset_image ( Finset.filter_subset_filter _ ( Finset.product_subset_product h h ) )

theorem highSums_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) : highSums m B ⊆ highSums m C := by
  exact Finset.image_subset_iff.mpr fun p hp => Finset.mem_image.mpr ⟨ p, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ h <| Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.1, h <| Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.2 ⟩, Finset.mem_filter.mp hp |>.2 ⟩, rfl ⟩

theorem collisions_mono {m : ℕ} {B C : Finset ℕ} (h : B ⊆ C) :
    collisions m B ⊆ collisions m C :=
  Finset.inter_subset_inter (lowSums_mono h) (highSums_mono h)

theorem mem_lowSums_lt {m : ℕ} {B : Finset ℕ} {v : ℕ} (hv : v ∈ lowSums m B) : v < m := by
  unfold lowSums at hv;
  grind

theorem mem_highSums_lt {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) {v : ℕ}
    (hv : v ∈ highSums m B) : v < m := by
  obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hv;
  rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_filter.mp hp, hB.1 p.1 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ), hB.1 p.2 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ]

/-
After deleting the minimum `α`, the value `α + β` is no longer a low pair sum, because
every remaining pair of distinct elements has both entries `≥ β > α`, so sum `> α + β`.
-/
theorem sum_not_lowSums_erase {m : ℕ} {S : Finset ℕ} {α β : ℕ} (hαβ : α < β)
    (hmin2 : ∀ x ∈ S, x ≠ α → β ≤ x) : α + β ∉ lowSums m (S.erase α) := by
  simp [lowSums];
  grind

/-! ### Reflection `-B = {m - b}` -/

/-- The reflected set `-B = {m - b : b ∈ B}`. -/
def reflB (m : ℕ) (B : Finset ℕ) : Finset ℕ := B.image (fun b : ℕ => m - b)

theorem card_reflB {m : ℕ} {B : Finset ℕ} (hB : FoldedOK m B) : (reflB m B).card = B.card := by
  rw [ reflB, Finset.card_image_of_injOn ];
  exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ hB.1 x hx, hB.1 y hy ] ;

theorem foldedOK_reflB {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    FoldedOK m (reflB m B) := by
  constructor;
  · intro b hb; obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hb; exact ⟨ Nat.sub_pos_of_lt ( hB.1 x hx |>.2 ), Nat.sub_lt ( by linarith ) ( hB.1 x hx |>.1 ) ⟩ ;
  · intro x hx y hy hxy;
    constructor;
    · obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx; obtain ⟨ b, hb, rfl ⟩ := Finset.mem_image.mp hy; simp_all +decide [ FoldedOK ] ;
      grind +ring;
    · simp_all +decide [ reflB ];
      intro z hz;
      obtain ⟨ a, ha, rfl ⟩ := hx; obtain ⟨ b, hb, rfl ⟩ := hy; have := hB.2 a ha b hb; simp_all +decide [ Nat.mod_eq_of_lt ] ;
      contrapose! this;
      have h_eq : (a + b) % m = z := by
        have h_eq : (a + b) % m = (m - (m - a + (m - b)) % m) % m := by
          simp +decide [ ← ZMod.natCast_eq_natCast_iff', Nat.cast_sub ( show a ≤ m from by linarith [ hB.1 a ha ] ), Nat.cast_sub ( show b ≤ m from by linarith [ hB.1 b hb ] ) ];
          rw [ Nat.cast_sub ( Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) ) ) ] ; simp +decide [ Nat.cast_sub ( show a ≤ m from by linarith [ hB.1 a ha ] ), Nat.cast_sub ( show b ≤ m from by linarith [ hB.1 b hb ] ) ] ; ring;
        rw [ h_eq, ← this, Nat.sub_sub_self ( show z ≤ m from by linarith [ hB.1 z hz ] ) ];
        exact Nat.mod_eq_of_lt ( hB.1 z hz |>.2 );
      exact ⟨ by aesop_cat, fun _ => h_eq.symm ▸ hz ⟩

theorem lowSums_reflB {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    lowSums m (reflB m B) = (highSums m B).image (fun v : ℕ => m - v) := by
  ext z;
  constructor;
  · unfold lowSums highSums;
    simp +zetaDelta at *;
    rintro x y hx hy hxy hxy' rfl; rcases Finset.mem_image.mp hx with ⟨ a, ha, rfl ⟩ ; rcases Finset.mem_image.mp hy with ⟨ b, hb, rfl ⟩ ; use a, b; simp_all +decide ;
    have := hB.1 a ha; have := hB.1 b hb; omega;
  · simp +zetaDelta at *;
    rintro x hx rfl;
    unfold highSums lowSums reflB at *;
    simp +zetaDelta at *;
    obtain ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, h ⟩, rfl ⟩ := hx; use a, b; simp_all +decide [ Nat.sub_sub, add_comm ] ;
    have := hB.1 a ha; have := hB.1 b hb; omega;

theorem highSums_reflB {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} :
    highSums m (reflB m B) = (lowSums m B).image (fun v : ℕ => m - v) := by
  ext z;
  simp [highSums, lowSums, reflB];
  constructor <;> intro h; all_goals grind

theorem collisions_reflB_card {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    (collisions m (reflB m B)).card = (collisions m B).card := by
  -- By definition of `collisions`, we know that `collisions m (reflB m B) = coll highSums m B ∩ lowSums m B|
  have h_collisions_refl : collisions m (reflB m B) = ((highSums m B) ∩ (lowSums m B)).image (fun v => m - v) := by
    convert congr_arg₂ ( fun x y => x ∩ y ) ( lowSums_reflB hm hB ) (highSums_reflB hm) using 1;
    ext; simp [highSums, lowSums];
    constructor; all_goals grind;
  rw [ h_collisions_refl, collisions ];
  rw [ Finset.inter_comm, Finset.card_image_of_injOn ];
  exact fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ mem_lowSums_lt ( Finset.mem_of_mem_inter_left hx ), mem_highSums_lt hm hB ( Finset.mem_of_mem_inter_right hy ) ] ;

/-! ### The core inductive step -/

theorem core_step {m : ℕ} (hm : 2 ≤ m) {S : Finset ℕ} (hS : FoldedOK m S) {α β : ℕ}
    (hα : α ∈ S) (hβ : β ∈ S) (hαβ : α < β) (hmin : ∀ x ∈ S, α ≤ x)
    (hmin2 : ∀ x ∈ S, x ≠ α → β ≤ x) (hsum : α + β < m)
    (IH : ∀ S', FoldedOK m S' → S'.card < S.card →
      4 * S'.card ≤ 4 * (collisions m S').card + m + 8) :
    4 * S.card ≤ 4 * (collisions m S).card + m + 8 := by
  by_cases hnc : α + β ∈ collisions m S;
  · obtain ⟨S', hS', hS'_card⟩ : ∃ S' : Finset ℕ, S' = S.erase α ∧ FoldedOK m S' ∧ S'.card < S.card ∧ (collisions m S').card + 1 ≤ (collisions m S).card := by
      refine' ⟨ S.erase α, rfl, foldedOK_subset hS ( Finset.erase_subset α S ), _, _ ⟩;
      · exact Finset.card_lt_card ( Finset.erase_ssubset hα );
      · refine' Nat.succ_le_of_lt ( Finset.card_lt_card _ );
        refine' ⟨ _, _ ⟩;
        · exact collisions_mono ( Finset.erase_subset _ _ );
        · rw [ Finset.not_subset ];
          refine' ⟨ α + β, hnc, _ ⟩;
          exact fun h => sum_not_lowSums_erase hαβ hmin2 <| Finset.mem_of_mem_inter_left h;
    grind;
  · linarith [ case2_bound hm hS hα hβ hαβ hmin hmin2 hsum hnc ]

/-! ### The folded additive lemma -/

/-
**Folded additive lemma.** For `m ≥ 2` and `B` satisfying `FoldedOK`,
`4 * |B| ≤ 4 * |C(B)| + m + 8`, i.e. `|B| - |C(B)| ≤ m/4 + 2`.
-/
theorem folded_additive {m : ℕ} (hm : 2 ≤ m) {B : Finset ℕ} (hB : FoldedOK m B) :
    4 * B.card ≤ 4 * (collisions m B).card + m + 8 := by
  by_contra! h_contra;
  -- By strong induction on B.card, we can assume the statement holds for all sets with cardinality less than B.card.
  induction' k : B.card using Nat.strong_induction_on with k ih generalizing B m;
  by_cases h_card : B.card ≤ 1;
  · grind;
  · -- Let α := B.min' (nonempty proof from card ≥ 2). Then hα : α ∈ B (Finset.min'_mem) and hmin : ∀ x ∈ B, α ≤ x (Finset.min'_le).
    obtain ⟨α, hα⟩ : ∃ α ∈ B, ∀ x ∈ B, α ≤ x := by
      exact ⟨ Nat.find <| Finset.card_pos.mp <| by linarith, Nat.find_spec <| Finset.card_pos.mp <| by linarith, fun x hx => Nat.find_min' _ hx ⟩
    obtain ⟨β, hβ⟩ : ∃ β ∈ B.erase α, ∀ x ∈ B.erase α, β ≤ x := by
      exact ⟨ Finset.min' _ ⟨ Classical.choose ( Finset.exists_mem_ne ( by linarith ) α ), Finset.mem_erase_of_ne_of_mem ( Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) α ) |>.2 ) ( Classical.choose_spec ( Finset.exists_mem_ne ( by linarith ) α ) |>.1 ) ⟩, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx ⟩
    have hαβ : α < β := by
      exact lt_of_le_of_ne ( hα.2 β ( Finset.mem_of_mem_erase hβ.1 ) ) ( by aesop )
    have hmin2 : ∀ x ∈ B, x ≠ α → β ≤ x := by
      exact fun x hx hx' => hβ.2 x ( Finset.mem_erase_of_ne_of_mem hx' hx )
    have hsum : α + β < m ∨ β + α > m := by
      have := hB.2 α hα.1 β ( Finset.mem_of_mem_erase hβ.1 ) ( by linarith ) ; omega;
    cases' hsum with hsum hsum;
    · exact absurd ( core_step hm hB hα.1 ( Finset.mem_of_mem_erase hβ.1 ) hαβ hα.2 hmin2 hsum fun S' hS' hS'_card => by specialize ih ( S'.card ) ( by linarith [ Finset.card_erase_lt_of_mem hα.1 ] ) hm hS'; aesop ) ( by linarith );
    · -- Let u := B.max' (nonempty), v := (B.erase u).max'. Then:
      obtain ⟨u, hu⟩ : ∃ u ∈ B, ∀ x ∈ B, x ≤ u := by
        exact ⟨ Finset.max' B ⟨ α, hα.1 ⟩, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
      obtain ⟨v, hv⟩ : ∃ v ∈ B.erase u, ∀ x ∈ B.erase u, x ≤ v := by
        exact ⟨ Finset.max' _ <| Finset.card_pos.mp <| by rw [ Finset.card_erase_of_mem hu.1 ] ; omega, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
      have hu_gt_v : u > v := by
        grind
      have huv_gt_m : u + v > m := by
        grind
      have huv_ne_m : u + v ≠ m := by
        grind
      generalize_proofs at *; (
      -- Let S := reflB m B, and consider α' := m - u, β' := m - v. Verify the core_step hypotheses for S with α', β':
      set S := reflB m B
      set α' := m - u
      set β' := m - v
      have hS : FoldedOK m S := by
        exact foldedOK_reflB hm hB
      have hα' : α' ∈ S := by
        exact Finset.mem_image.mpr ⟨ u, hu.1, rfl ⟩
      have hβ' : β' ∈ S := by
        exact Finset.mem_image.mpr ⟨ v, Finset.mem_of_mem_erase hv.1, rfl ⟩
      have hα'β' : α' < β' := by
        exact Nat.sub_lt_sub_left ( by linarith [ hB.1 u hu.1, hB.1 v ( Finset.mem_of_mem_erase hv.1 ) ] ) hu_gt_v
      have hmin' : ∀ z ∈ S, α' ≤ z := by
        simp +zetaDelta at *;
        simp +decide [ reflB ];
        grind
      have hmin2' : ∀ z ∈ S, z ≠ α' → β' ≤ z := by
        simp +zetaDelta at *;
        simp_all +decide [ reflB ];
        grind +qlia
      have hsum' : α' + β' < m := by
        rw [ tsub_add_tsub_comm ] <;> try linarith [ hB.1 u hu.1, hB.1 v ( Finset.mem_of_mem_erase hv.1 ) ] ;
        grind
      generalize_proofs at *; (
      -- Apply the core_step lemma to S with α' and β'.
      have h_core_step : 4 * S.card ≤ 4 * (collisions m S).card + m + 8 := by
        apply core_step hm hS hα' hβ' hα'β' hmin' hmin2' hsum' (fun S' hS' hS'_card => by
          exact le_of_not_gt fun h => ih _ ( by linarith [ show #S = #B from card_reflB hB ] ) hm hS' h rfl)
      generalize_proofs at *; (
      grind +suggestions)))

-- ============================================================
-- Folding
-- ============================================================

open scoped BigOperators
open Finset

/-
For a triple-free set `A` with pivot `h ∈ A` and `h ≥ 2`, the folded coordinate set
`B_h` satisfies the hypothesis of the folded additive lemma modulo `h`.
-/
theorem foldedOK_Bset {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A)
    (hh2 : 2 ≤ h) : FoldedOK h (Bset A N h) := by
  constructor;
  · exact fun x hx => by unfold Bset at hx; unfold Xset at hx; unfold Yset at hx; aesop;
  · intro x hx y hy hxy; refine' ⟨ _, _ ⟩ <;> contrapose! hxy <;> simp_all +decide [ Bset, Xset, Yset ] ;
    · unfold IsTripleFree at hA; simp_all +decide [ HasTriple ] ;
      grind +ring;
    · -- If $x + y \geq h$, then $(x + y) \% h = x + y - h$, which is in $A$.
      by_cases hxy_ge_h : x + y ≥ h;
      · have hxy_mod : (x + y) % h = x + y - h := by
          rw [ Nat.mod_eq_sub_mod hxy_ge_h ];
          rw [ Nat.mod_eq_of_lt ( by omega ) ];
        contrapose! hA; simp_all +decide [ IsTripleFree ] ;
        use x, hx.1.2, y, hy.1.2, h, hh;
        grind;
      · simp_all +decide [ Nat.mod_eq_of_lt ( not_le.mp hxy_ge_h ) ];
        unfold IsTripleFree at hA; simp_all +decide [ HasTriple ] ;
        grind +ring

/-
Collisions of `B_h` land in the "excluded" set `E`.
-/
theorem collisions_subset_Eset {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A) :
    collisions h (Bset A N h) ⊆ Eset A N h := by
  intro r hr;
  refine' Finset.mem_sdiff.mpr ⟨ _, _ ⟩;
  · unfold collisions at hr;
    unfold lowSums highSums at hr;
    grind;
  · simp_all +decide [ collisions, lowSums, highSums, Xset, Yset ];
    constructor <;> intros <;> simp_all +decide [ Bset ];
    · obtain ⟨ ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, hb₁, hb₂ ⟩, hab, hlt ⟩, rfl ⟩, c, d, ⟨ ⟨ ⟨ hc₁, hc₂ ⟩, hd₁, hd₂ ⟩, hcd, hlt' ⟩, hcd' ⟩ := hr;
      contrapose! hA;
      unfold IsTripleFree; simp_all +decide [ Xset, Yset ] ;
      exact ⟨ a, ha₁.2, b, hb₁.2, h, hh, by omega, by omega, by omega, by ring_nf at *; aesop ⟩;
    · obtain ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ⟨ hb₁, hb₂ ⟩ ⟩, hab, hlt ⟩, rfl ⟩ := hr.2;
      contrapose! hA;
      unfold IsTripleFree; simp_all +decide [ Xset, Yset ] ;
      use a, ha₁.2, b, hb₁.2, h, hh;
      grind

/-
The elementary counting identity `|X| + |Y| + |E| = (h-1) + |B_h|`.
-/
theorem card_XY_E (A : Finset ℕ) (N h : ℕ) :
    (Xset A h).card + (Yset A N h).card + (Eset A N h).card = (h - 1) + (Bset A N h).card := by
  rw [ Eset, Finset.card_sdiff ];
  rw [ ← Finset.card_union_add_card_inter, Bset ];
  rw [ show ( Xset A h ∪ Yset A N h ) ∩ Ico 1 h = Xset A h ∪ Yset A N h from ?_ ];
  · rw [ add_right_comm, Nat.add_sub_of_le ];
    · simp +arith +decide;
    · exact Finset.card_le_card ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) );
  · exact Finset.inter_eq_left.mpr ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )

/-
**Folding lemma.** For a triple-free `A` and pivot `h ∈ A`,
`4(|X|+|Y|) + 4|E \ C(B_h)| ≤ 5h + 4`, i.e. `|X|+|Y| ≤ 5h/4 - |E \ C(B_h)| + 1`.
-/
theorem folding_lemma {A : Finset ℕ} {N h : ℕ} (hA : IsTripleFree A) (hh : h ∈ A) :
    4 * ((Xset A h).card + (Yset A N h).card)
      + 4 * (Eset A N h \ collisions h (Bset A N h)).card ≤ 5 * h + 4 := by
  by_cases h_ge_2 : 2 ≤ h;
  · -- By the folding lemma, we have $4 * |B_h| \leq 4 * |C(B_h)| + h + 8$.
    have h_folding : 4 * (Bset A N h).card ≤ 4 * (collisions h (Bset A N h)).card + h + 8 := by
      exact Erdos865.folded_additive h_ge_2 ( Erdos865.foldedOK_Bset hA hh h_ge_2 );
    have h_collisions_subset_Eset : (collisions h (Bset A N h)).card + #(Eset A N h \ collisions h (Bset A N h)) = (Eset A N h).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · rw [ Finset.union_sdiff_of_subset ( collisions_subset_Eset hA hh ) ];
      · exact Finset.disjoint_sdiff;
    linarith [ card_XY_E A N h, Nat.sub_add_cancel ( by linarith : 1 ≤ h ) ];
  · interval_cases h <;> simp_all +decide [ Xset, Yset, Eset, Bset ]

-- ============================================================
-- UpperBound
-- ============================================================

open scoped BigOperators
open Finset

/-
Counting bound: every element of `A ⊆ [1,N]` is counted by `X`, by `Y`, is one of the
two endpoints `h, 2h`, or lies in the tail `(2h, N]`.
-/
theorem card_A_bound {A : Finset ℕ} {N : ℕ} (hsub : A ⊆ Finset.Icc 1 N) (h : ℕ) :
    A.card ≤ (Xset A h).card + (Yset A N h).card + 2 + (N - 2 * h) := by
  -- Let's show that $A$ is a subset of $Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2*h} ∪ Finset.Icc (2*h + 1) N$.
  have h_subset : A ⊆ Xset A h ∪ (Yset A N h).image (fun r => h + r) ∪ {h, 2 * h} ∪ Finset.Icc (2 * h + 1) N := by
    intro a ha; by_cases ha1 : a < h <;> by_cases ha2 : a = h <;> by_cases ha3 : a = 2 * h <;> simp_all +decide [ Finset.subset_iff ] ;
    · exact Or.inl <| Finset.mem_filter.mpr ⟨ Finset.mem_Ico.mpr ⟨ by linarith [ hsub ha ], ha1 ⟩, ha ⟩;
    · by_cases ha4 : a < 2 * h <;> simp_all +decide [ Xset, Yset ];
      · exact Or.inr <| Or.inl ⟨ a - h, ⟨ ⟨ Nat.sub_pos_of_lt <| lt_of_le_of_ne ha1 <| Ne.symm ha2, by omega ⟩, by linarith [ hsub ha, Nat.sub_add_cancel ha1 ], by convert ha using 1; omega ⟩, by omega ⟩;
      · exact Or.inr <| Or.inr <| lt_of_le_of_ne ha4 <| Ne.symm ha3;
  refine le_trans ( Finset.card_le_card h_subset ) ?_;
  refine' le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_le_card ( Finset.Subset.refl _ ) ) ( Finset.card_image_le ) ) ) ( Finset.card_insert_le _ _ ) ) ) ( by simp +arith +decide [ Nat.card_Icc ] ) )

/-
The open interval `(p, q)` contains no element of `A`.
-/
theorem gap_empty {A : Finset ℕ} {H p q : ℕ} (hqlo : H ≤ q)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    ∀ a ∈ A, ¬ (p < a ∧ a < q) := by
  grind +qlia

/-
Case 1 interval `I = (max(p, N-h), h)` is contained in `E \ C(B_h)` for `h = q`.
-/
theorem case1_I_sub {A : Finset ℕ} {H p q : ℕ} (hqlo : H ≤ q)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Finset.Ico (max p (2 * H - q) + 1) q ⊆
      Eset A (2 * H) q \ collisions q (Bset A (2 * H) q) := by
  intro x hx; simp_all +decide [ Eset, Bset ] ;
  refine' ⟨ ⟨ by linarith, _, _ ⟩, _ ⟩ <;> simp_all +decide [ Xset, Yset, collisions ];
  · grind;
  · grind;
  · intro hx₁ hx₂; simp_all +decide [ lowSums, highSums ] ;
    omega

/-
**Case 1** (`s ≤ 4e`): folding around `h = q`.
-/
theorem even_bound_case1 {H p q : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) (hq : q ∈ A) (hqlo : H ≤ q) (hqhi : q ≤ 2 * H)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hp : p ∈ A) (hplo : 1 ≤ p) (hphi : p ≤ H)
    (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) (hcase : q - H ≤ 4 * (H - p)) :
    4 * A.card ≤ 5 * H + 24 := by
  have := @folding_lemma A ( 2 * H ) q ?_ ?_ <;> simp_all +decide [ Finset.card_image_of_injective, Function.Injective ];
  have hIle := Finset.card_le_card ( case1_I_sub hqlo hqmin hpmax : Finset.Ico ( Max.max p ( 2 * H - q ) + 1 ) q ⊆ Eset A ( 2 * H ) q \ collisions q ( Bset A ( 2 * H ) q ) ) ; simp_all +decide [ Nat.card_Ico ] ;
  have hcount := card_A_bound hsub q; simp_all +decide [ Nat.card_Ico ] ;
  omega

/-
In case 2 (`h = p`), the folded coordinate set avoids `[1, q-p-1]`, since for
`1 ≤ r < q - p` the partner `p + r` lies in the empty gap `(p, q)`.
-/
theorem case2_Bset_disjoint {A : Finset ℕ} {H p q : ℕ}
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Bset A (2 * H) p ∩ Finset.Ico 1 (q - p) = ∅ := by
  simp +decide [ Bset, Yset ];
  grind +splitIndPred

/-
Case 2 interval `I = [1, t] \ A` (with `t = q - p - 1`) is contained in `E \ C(B_p)`,
provided `q - p ≤ p` (so the interval sits below the pivot).
-/
theorem case2_I_sub {A : Finset ℕ} {H p q : ℕ} (hple : q - p ≤ p)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) :
    Finset.Ico 1 (q - p) \ A ⊆ Eset A (2 * H) p \ collisions p (Bset A (2 * H) p) := by
  intro x hx; simp_all +decide [ Finset.subset_iff ] ;
  constructor;
  · simp_all +decide [ Eset, Xset, Yset ];
    grind +splitImp;
  · intro hx';
    obtain ⟨ y, hy, z, hz, hyz, rfl ⟩ := Finset.mem_image.mp ( Finset.mem_inter.mp hx' |>.1 );
    simp_all +decide [ Bset, Xset, Yset ];
    grind

/-- A subset of a triple-free set is triple-free. -/
theorem tripleFree_subset {A B : Finset ℕ} (hA : IsTripleFree A) (h : B ⊆ A) :
    IsTripleFree B := by
  intro ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hab', hac', hbc'⟩
  exact hA ⟨a, h ha, b, h hb, c, h hc, hab, hac, hbc, h hab', h hac', h hbc'⟩

/-
**Case 2** (`s > 4e`): folding around `h = p`, using the induction hypothesis on
`A ∩ [1, q-p-1]`.
-/
theorem even_bound_case2 {H p q : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) (hqlo : H ≤ q) (hqhi : q ≤ 2 * H)
    (hqmin : ∀ a ∈ A, H ≤ a → q ≤ a) (hp : p ∈ A) (hplo : 1 ≤ p) (hphi : p ≤ H)
    (hpmax : ∀ a ∈ A, a ≤ H → a ≤ p) (hcase : 4 * (H - p) < q - H)
    (IH : ∀ H' (A' : Finset ℕ), H' < H → A' ⊆ Finset.Icc 1 (2 * H') → IsTripleFree A' →
      4 * A'.card ≤ 5 * H' + 24) :
    4 * A.card ≤ 5 * H + 24 := by
  by_cases hq_p : p < q - p;
  · have hAsub : A ⊆ Finset.Icc 1 p ∪ Finset.Icc q (2 * H) := by
      grind;
    have := Finset.card_mono hAsub; simp_all +decide [ Finset.card_union ] ;
    omega;
  · -- Apply the folding_lemma to get the inequality involving the cardinalities of Xset, Yset, and Eset.
    have h_fold : 4 * ((Xset A p).card + (Yset A (2 * H) p).card) + 4 * (Eset A (2 * H) p \ collisions p (Bset A (2 * H) p)).card ≤ 5 * p + 4 := by
      apply folding_lemma hA hp;
    have h_I_sub : (Finset.Ico 1 (q - p) \ A) ⊆ Eset A (2 * H) p \ collisions p (Bset A (2 * H) p) := by
      apply case2_I_sub (by
      omega) hqmin hpmax;
    have h_A0 : 4 * (A ∩ Finset.Ico 1 (q - p)).card ≤ 5 * ((q - p) / 2) + 24 := by
      apply IH ((q - p) / 2) (A ∩ Finset.Ico 1 (q - p));
      · omega;
      · grind;
      · exact tripleFree_subset hA ( Finset.inter_subset_left );
    have h_card_A : A.card ≤ (Xset A p).card + (Yset A (2 * H) p).card + 2 + (2 * H - 2 * p) := by
      apply card_A_bound hsub p;
    have h_card_Ico : (Finset.Ico 1 (q - p)).card = (Finset.Ico 1 (q - p) \ A).card + (A ∩ Finset.Ico 1 (q - p)).card := by
      grind;
    have := Finset.card_le_card h_I_sub; simp_all +decide ;
    omega

/-
The even-`N` upper bound: every triple-free `A ⊆ [1, 2H]` has `4|A| ≤ 5H + 24`,
i.e. `|A| ≤ 5H/4 + 6`. Proved by strong induction on `H`.
-/
theorem even_bound (H : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 (2 * H))
    (hA : IsTripleFree A) : 4 * A.card ≤ 5 * H + 24 := by
  induction' H using Nat.strong_induction_on with H ih generalizing A;
  by_cases h1 : (A ∩ Finset.Icc H (2 * H)).Nonempty;
  · by_cases h2 : (A ∩ Finset.Icc 1 H).Nonempty;
    · -- Let $q = \min(A \cap [H, 2H])$ and $p = \max(A \cap [1, H])$.
      obtain ⟨q, hq⟩ : ∃ q ∈ A, H ≤ q ∧ q ≤ 2 * H ∧ ∀ a ∈ A, H ≤ a → q ≤ a := by
        exact ⟨ Nat.find h1, Nat.find_spec h1 |> fun x => Finset.mem_of_mem_inter_left x, Nat.find_spec h1 |> fun x => Finset.mem_Icc.mp ( Finset.mem_inter.mp x |>.2 ) |>.1, Nat.find_spec h1 |> fun x => Finset.mem_Icc.mp ( Finset.mem_inter.mp x |>.2 ) |>.2, fun a ha ha' => Nat.find_min' h1 <| Finset.mem_inter.mpr ⟨ ha, Finset.mem_Icc.mpr ⟨ ha', by linarith [ Finset.mem_Icc.mp ( hsub ha ) ] ⟩ ⟩ ⟩
      obtain ⟨p, hp⟩ : ∃ p ∈ A, 1 ≤ p ∧ p ≤ H ∧ ∀ a ∈ A, a ≤ H → a ≤ p := by
        obtain ⟨p, hp⟩ : ∃ p ∈ A ∩ Finset.Icc 1 H, ∀ a ∈ A ∩ Finset.Icc 1 H, a ≤ p := by
          exact ⟨ Finset.max' _ h2, Finset.max'_mem _ h2, fun a ha => Finset.le_max' _ _ ha ⟩;
        exact ⟨ p, Finset.mem_of_mem_inter_left hp.1, Finset.mem_Icc.mp ( Finset.mem_inter.mp hp.1 |>.2 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_inter.mp hp.1 |>.2 ) |>.2, fun a ha ha' => hp.2 a ( Finset.mem_inter.mpr ⟨ ha, Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( hsub ha ) |>.1, ha' ⟩ ⟩ ) ⟩;
      by_cases hcase : q - H ≤ 4 * (H - p);
      · apply even_bound_case1 hsub hA hq.left hq.right.left hq.right.right.left hq.right.right.right hp.left hp.right.left hp.right.right.left hp.right.right.right hcase;
      · apply even_bound_case2 hsub hA hq.right.left hq.right.right.left hq.right.right.right hp.left hp.right.left hp.right.right.left hp.right.right.right (by omega) (fun H' A' h1 h2 h3 => ih H' h1 A' h2 h3);
    · simp_all +decide [ Finset.ext_iff ];
      have := Finset.card_le_card ( show A ⊆ Finset.Icc ( H + 1 ) ( 2 * H ) from fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ h2 x hx ( Finset.mem_Icc.mp ( hsub hx ) |>.1 ) ], by linarith [ Finset.mem_Icc.mp ( hsub hx ) |>.2 ] ⟩ ) ; simp_all +arith +decide;
      omega;
  · rcases H with ( _ | H ) <;> simp_all +decide [ Finset.Nonempty ];
    exact le_trans ( Nat.mul_le_mul_left _ ( Finset.card_le_card ( show A ⊆ Finset.Icc 1 ( H + 1 ) from fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( hsub hx ) |>.1, Nat.le_of_not_lt fun hx' => by linarith [ Finset.mem_Icc.mp ( hsub hx ) |>.2, h1 x hx ( by linarith ) ] ⟩ ) ) ) ( by simp +arith +decide )

-- ============================================================
-- Sharpness
-- ============================================================

open scoped BigOperators
open Finset

/-- The sharpness construction `A = [M, 2M] ∪ [4M, 8M]`. -/
def sharpSet (M : ℕ) : Finset ℕ := Finset.Icc M (2 * M) ∪ Finset.Icc (4 * M) (8 * M)

/-- The construction sits inside `[1, 8M]` (for `M ≥ 1`). -/
theorem sharpSet_subset {M : ℕ} (hM : 1 ≤ M) : sharpSet M ⊆ Finset.Icc 1 (8 * M) :=
  Finset.union_subset (Finset.Icc_subset_Icc (by linarith) (by linarith))
    (Finset.Icc_subset_Icc (by linarith) (by linarith))

/-- The construction has `5M + 2` elements. -/
theorem sharpSet_card {M : ℕ} (hM : 1 ≤ M) : (sharpSet M).card = 5 * M + 2 := by
  have hdisj : Disjoint (Finset.Icc M (2 * M)) (Finset.Icc (4 * M) (8 * M)) :=
    Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
      simp only [Finset.mem_Icc] at hx₁ hx₂; omega
  rw [sharpSet, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Icc]
  omega

/-- The construction is triple-free. -/
theorem sharpSet_tripleFree (M : ℕ) : IsTripleFree (sharpSet M) := by
  intro h;
  obtain ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, hab', hac', hbc' ⟩ := h;
  unfold sharpSet at *;
  grind

/-- Sharpness: for `N = 8M` with `M ≥ 1` there is a triple-free subset of `[1,N]`
of size `5M + 2`, i.e. with `8 * card = 5 * N + 16`. -/
theorem sharpness {M : ℕ} (hM : 1 ≤ M) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (8 * M) ∧ IsTripleFree A ∧
      8 * A.card = 5 * (8 * M) + 16 := by
  refine ⟨sharpSet M, sharpSet_subset hM, sharpSet_tripleFree M, ?_⟩
  rw [sharpSet_card hM]; ring

-- ============================================================
-- Main
-- ============================================================

/-!
# A sharp `5/8` bound for Erdős Problem 865

For `A ⊆ {1, …, N}` we say `A` contains a *pairwise-sum triple* if there are distinct
`a, b, c ∈ A` with `a + b, a + c, b + c ∈ A` (`Erdos865.HasTriple`). Let `f₃(N)` be the least
size forcing such a triple. This file assembles the proof that
`f₃(N) = 5N/8 + O(1)`, resolving Erdős Problem 865.

* `Erdos865.erdos865_upper_bound` — every triple-free `A ⊆ [1,N]` has `8|A| ≤ 5N + 53`,
  i.e. `|A| ≤ 5N/8 + O(1)`.
* `Erdos865.erdos865_contains_triple` — every `A ⊆ [1,N]` with `8|A| > 5N + 53` contains a
  pairwise-sum triple (the contrapositive form matching the paper's Theorem 1.1).
* `Erdos865.erdos865_threshold` — the packaged existence statement `∃ C, …`.
* `Erdos865.sharpness` — for `N = 8M` (`M ≥ 1`) there is a triple-free `A ⊆ [1,N]` with
  `8|A| = 5N + 16`, so the constant `5/8` is optimal.
-/

open scoped BigOperators
open Finset

/-- **Upper bound (Erdős 865).** Every triple-free set `A ⊆ [1,N]` satisfies
`8 * |A| ≤ 5 * N + 53`, i.e. `|A| ≤ (5/8) N + O(1)`. -/
theorem erdos865_upper_bound (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 N)
    (hA : IsTripleFree A) : 8 * A.card ≤ 5 * N + 53 := by
  have hsub' : A ⊆ Finset.Icc 1 (2 * ((N + 1) / 2)) :=
    hsub.trans (Finset.Icc_subset_Icc_right (by omega))
  have h := even_bound ((N + 1) / 2) A hsub' hA
  omega

/-- **Contains a triple (Erdős 865, Theorem 1.1 form).** Every `A ⊆ [1,N]` with
`5 * N + 53 < 8 * |A|` (i.e. `|A| ≥ (5/8) N + O(1)`) contains a pairwise-sum triple. -/
theorem erdos865_contains_triple (N : ℕ) (A : Finset ℕ) (hsub : A ⊆ Finset.Icc 1 N)
    (hcard : 5 * N + 53 < 8 * A.card) : HasTriple A := by
  by_contra h
  have := erdos865_upper_bound N A hsub h
  omega

/-- The upper bound packaged as an existence statement: there is an absolute constant `C`
such that every triple-free `A ⊆ [1,N]` has `8 * |A| ≤ 5 * N + C`. -/
theorem erdos865_threshold : ∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
    IsTripleFree A → 8 * A.card ≤ 5 * N + C :=
  ⟨53, erdos865_upper_bound⟩

/-- **Erdős Problem 865 (Erdős–Sós pairwise-sums, k = 3).** Proved by Cipollini and
GPT-5.5 Pro [Ci26]: there is a constant `C` such that every `A ⊆ {1,…,N}` with
`|A| ≥ (5/8) N + C` contains distinct `a, b, c ∈ A` whose three pairwise sums
`a+b, a+c, b+c` all lie in `A`. Moreover, `5/8` is best possible: for every `M ≥ 1`,
`N = 8M`, the set `[M, 2M] ∪ [4M, 8M] ⊂ {1,…,N}` is triple-free and has
`5M + 2 = (5/8) N + 2` elements. -/
theorem erdos_865 :
    (∃ C : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Finset.Icc 1 N →
        IsTripleFree A → 8 * A.card ≤ 5 * N + C) ∧
    (∀ M : ℕ, 1 ≤ M →
        ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (8 * M) ∧ IsTripleFree A ∧
          8 * A.card = 5 * (8 * M) + 16) :=
  ⟨erdos865_threshold, fun _ hM => sharpness hM⟩

#print axioms erdos_865
-- 'Erdos865.erdos_865' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos865
