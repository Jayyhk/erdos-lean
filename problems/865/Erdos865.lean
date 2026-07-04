import Mathlib

namespace Erdos865

-- ============================================================
-- Defs
-- ============================================================

open scoped BigOperators
open Finset


/-!
# Erdős problem 865 — core definitions

We work with finite subsets `A : Finset ℕ`.  A set "contains a triple" if there are
three distinct elements `a, b, c ∈ A` all of whose pairwise sums lie in `A`.
A set is *bad* if it contains no such triple.

The constraint `A ⊆ {1,…,N}` is expressed by the predicate `MemRange N A`.
-/

/-- `A ⊆ {1, …, N}`. -/
def MemRange (N : ℕ) (A : Finset ℕ) : Prop := ∀ x ∈ A, 1 ≤ x ∧ x ≤ N

/-- `A` contains three distinct elements whose three pairwise sums all lie in `A`. -/
def HasTriple (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b ∈ A ∧ a + c ∈ A ∧ b + c ∈ A

/-- `A` is *bad* if it contains no admissible triple. -/
def IsBad (A : Finset ℕ) : Prop := ¬ HasTriple A

/-! ## Folded additive sets (used in Lemma 1) -/

/-- The set of residues occurring as a *non-wrapped* sum `x + y` of two distinct elements
of `B`, with `x + y < m`. -/
noncomputable def lowSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (((B ×ˢ B).filter (fun p => p.1 < p.2 ∧ p.1 + p.2 < m)).image (fun p => p.1 + p.2))

/-- The set of residues occurring as a *wrapped* sum `x + y - m` of two distinct elements
of `B`, with `x + y > m`. -/
noncomputable def highSums (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (((B ×ˢ B).filter (fun p => p.1 < p.2 ∧ m < p.1 + p.2)).image (fun p => p.1 + p.2 - m))

/-- Residues that occur both as a low (non-wrapped) and a high (wrapped) sum. -/
noncomputable def collisions (m : ℕ) (B : Finset ℕ) : Finset ℕ :=
  lowSums m B ∩ highSums m B

/-- The hypothesis of Lemma 1: `B ⊆ {1,…,m-1}` and no two distinct elements of `B`
have sum `≡ 0 (mod m)` or `≡ an element of B (mod m)`. -/
def FoldedOK (m : ℕ) (B : Finset ℕ) : Prop :=
  (∀ x ∈ B, 1 ≤ x ∧ x < m) ∧
  (∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ (m ∣ (x + y)) ∧ (x + y) % m ∉ B)

/-! ## Folding a bad set around a pivot `h` (used in Lemma 2) -/

/-- `X = { r : 1 ≤ r < h, r ∈ A }`. -/
noncomputable def Xset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => r ∈ A)

/-- `Y = { r : 1 ≤ r < h, h + r ∈ A }` (with the automatic constraint `h + r ≤ N` coming
from `MemRange N A`). -/
noncomputable def Yset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h).filter (fun r => h + r ∈ A)

/-- `B = X ∩ Y`: the residues `r` with both `r` and `h + r` in `A`. -/
noncomputable def Bset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  Xset h A ∩ Yset h A

/-- `E = {1,…,h-1} \ (X ∪ Y)`. -/
noncomputable def Eset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Ico 1 h) \ (Xset h A ∪ Yset h A)


-- ============================================================
-- Lemma1
-- ============================================================

set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset


/-!
# Lemma 1 — the folded additive lemma

We prove: there is an absolute constant `K₁` such that for every `m ≥ 2` and every `B`
satisfying `FoldedOK m B`, one has `|B| − |C(B)| ≤ m/4 + K₁`.

The proof is by strong induction on `|B|`, using:
* `negSet` reflection symmetry to reduce to the case where the two smallest elements have
  sum `< m`;
* the four-set bound `four_set_bound` for the base case (the two smallest sum is not a
  collision);
* the deletion step `collisions_erase_lt` for the inductive case.
-/

/-- Reflection `B ↦ {m − b : b ∈ B}` modulo `m`. -/
noncomputable def negSet (m : ℕ) (B : Finset ℕ) : Finset ℕ := B.image (fun b => m - b)

/-
Reflection preserves the cardinality.
-/
theorem negSet_card (m : ℕ) (B : Finset ℕ) (hB : FoldedOK m B) :
    (negSet m B).card = B.card := by
  exact Finset.card_image_of_injOn fun x hx y hy hxy => by have := hB.1 x hx; have := hB.1 y hy; omega;

/-
Reflection preserves the `FoldedOK` hypothesis.
-/
theorem negSet_foldedOK (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    FoldedOK m (negSet m B) := by
  constructor <;> intro x hx <;> simp_all +decide [ negSet ];
  · rcases hx with ⟨ a, ha, rfl ⟩ ; exact ⟨ Nat.sub_pos_of_lt ( hB.1 a ha |>.2 ), Nat.sub_lt ( by linarith ) ( hB.1 a ha |>.1 ) ⟩ ;
  · obtain ⟨ a, ha, rfl ⟩ := hx; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    intro b hb hab;
    have h_mod : (m - a + (m - b)) % m = (2 * m - (a + b)) % m := by
      rw [ show 2 * m - ( a + b ) = m - a + ( m - b ) by rw [ two_mul, tsub_add_tsub_comm ] <;> linarith [ hB.1 a ha, hB.1 b hb ] ];
    have h_mod : (2 * m - (a + b)) % m = (m - (a + b) % m) % m := by
      zify;
      rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ two_mul, Int.add_emod, Int.sub_emod ];
      · exact Nat.le_of_lt ( Nat.mod_lt _ ( by linarith ) );
      · linarith [ hB.1 a ha, hB.1 b hb ];
    have h_mod : (m - (a + b) % m) % m = m - (a + b) % m := by
      rw [ Nat.mod_eq_of_lt ];
      exact Nat.sub_lt ( by linarith ) ( Nat.pos_of_ne_zero fun h => by have := hB.2 a ha b hb ( by aesop ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] );
    have := hB.2 a ha b hb ( by aesop ) ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    exact ⟨ Nat.sub_ne_zero_of_lt ( Nat.mod_lt _ ( by linarith ) ), fun x hx hx' => this.2 <| by convert hx using 1; rw [ tsub_right_inj ] at hx' <;> linarith [ Nat.mod_lt ( a + b ) ( by linarith : 0 < m ), hB.1 x hx, hB.1 a ha, hB.1 b hb ] ⟩

/-
Low sums of the reflection are the reflected high sums.
-/
theorem lowSums_negSet (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    lowSums m (negSet m B) = (highSums m B).image (fun r => m - r) := by
  ext r; simp [lowSums, highSums, negSet];
  constructor <;> rintro ⟨ a, b, h, rfl ⟩ <;> use a, b <;> simp_all +decide [ Nat.sub_sub ];
  · have := hB.1 a h.1.2; have := hB.1 b h.1.1; omega;
  · have := hB.1 a h.1.1; have := hB.1 b h.1.2; omega;

/-
High sums of the reflection are the reflected low sums.
-/
theorem highSums_negSet (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    highSums m (negSet m B) = (lowSums m B).image (fun r => m - r) := by
  ext r;
  simp +zetaDelta at *;
  constructor <;> intro hr;
  · obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hr;
    obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.1 ) ; obtain ⟨ y, hy, hy' ⟩ := Finset.mem_image.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_product.mp |>.2 ) ; use x + y; simp_all +decide [ lowSums ] ;
    exact ⟨ ⟨ y, x, ⟨ ⟨ hy, hx ⟩, by omega, by omega ⟩, by ring ⟩, by omega ⟩;
  · rcases hr with ⟨ r, hr, rfl ⟩ ; unfold lowSums highSums negSet at *; simp_all +decide [ Finset.mem_image ] ;
    grind

/-
Reflection preserves the number of collisions.
-/
theorem negSet_collisions_card (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B) :
    (collisions m (negSet m B)).card = (collisions m B).card := by
  -- By definition of `collisions`, we have:
  have h_collisions : collisions m (negSet m B) = (collisions m B).image (fun r => m - r) := by
    ext; simp [collisions, lowSums_negSet, highSums_negSet];
    constructor <;> intro h <;> simp_all +decide [ lowSums_negSet, highSums_negSet ];
    · rcases h with ⟨ ⟨ a, ha, rfl ⟩, ⟨ b, hb, hab ⟩ ⟩ ; use b; simp_all +decide [ Nat.sub_eq_iff_eq_add ] ;
      convert ha using 1;
      unfold lowSums highSums at *; simp_all +decide [ Finset.mem_image ] ;
      grind;
    · grind;
  rw [ h_collisions, Finset.card_image_of_injOn ];
  intro x hx y hy; rw [ tsub_right_inj ] <;> norm_num at *;
  · exact Finset.mem_inter.mp hx |>.1 |> fun h => Finset.mem_image.mp h |> fun ⟨ p, hp₁, hp₂ ⟩ => by linarith [ Finset.mem_filter.mp hp₁ |>.2.2 ] ;
  · unfold collisions at hx hy; simp_all +decide [ lowSums, highSums ] ;
    grind

/-
Erasing an element preserves the `FoldedOK` hypothesis.
-/
theorem FoldedOK_erase (m : ℕ) (B : Finset ℕ) (a : ℕ) (hB : FoldedOK m B) :
    FoldedOK m (B.erase a) := by
  simp_all +decide [ FoldedOK ]

/-
A four-set Bonferroni inequality: the sum of the cardinalities is at most the cardinality
of the union plus the sum of the six pairwise intersection cardinalities.
-/
theorem card_sum_le_union_add_pairwise {α : Type*} [DecidableEq α]
    (T1 T2 T3 T4 : Finset α) :
    T1.card + T2.card + T3.card + T4.card ≤
      (T1 ∪ T2 ∪ T3 ∪ T4).card +
        ((T1 ∩ T2).card + (T1 ∩ T3).card + (T1 ∩ T4).card +
          (T2 ∩ T3).card + (T2 ∩ T4).card + (T3 ∩ T4).card) := by
  simp +arith +decide [ ← add_assoc, Finset.card_union_add_card_inter ];
  rw [ Finset.card_union, Finset.card_union, Finset.card_union ];
  rw [ show T2 ∩ ( T3 ∪ T4 ) = ( T2 ∩ T3 ) ∪ ( T2 ∩ T4 ) by rw [ Finset.inter_union_distrib_left ], show T1 ∩ ( T2 ∪ ( T3 ∪ T4 ) ) = ( T1 ∩ T2 ) ∪ ( T1 ∩ ( T3 ∪ T4 ) ) by rw [ Finset.inter_union_distrib_left ], show T1 ∩ ( T3 ∪ T4 ) = ( T1 ∩ T3 ) ∪ ( T1 ∩ T4 ) by rw [ Finset.inter_union_distrib_left ] ];
  grind

/-! ### The four sets in `ZMod m` for the four-set bound -/

/-- `T1 = {x : x ∈ B}` in `ZMod m`. -/
noncomputable def fsT1 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  B.image (fun x : ℕ => (x : ZMod m))
/-- `T2 = {-x : x ∈ B}` in `ZMod m`. -/
noncomputable def fsT2 (m : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  B.image (fun x : ℕ => -(x : ZMod m))
/-- `T3 = {x - a : x ∈ B} \ {0}` in `ZMod m`. -/
noncomputable def fsT3 (m a : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  (B.image (fun x : ℕ => (x : ZMod m) - (a : ZMod m))).erase 0
/-- `T4 = {b - x : x ∈ B} \ {0}` in `ZMod m`. -/
noncomputable def fsT4 (m b : ℕ) (B : Finset ℕ) : Finset (ZMod m) :=
  (B.image (fun x : ℕ => (b : ZMod m) - (x : ZMod m))).erase 0

/-
In the cyclic group `ZMod m`, the equation `t + t = w` has at most two solutions among
the (distinct) residues of `B`.
-/
theorem card_two_mul_fiber_le (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hBlt : ∀ x ∈ B, x < m)
    (w : ZMod m) :
    (B.filter (fun x : ℕ => (x : ZMod m) + (x : ZMod m) = w)).card ≤ 2 := by
  by_contra! h_contra;
  obtain ⟨x, y, z, hx, hy, hz, hxy, hyz, hxz⟩ : ∃ x y z : ℕ, x ∈ B ∧ y ∈ B ∧ z ∈ B ∧ x < m ∧ y < m ∧ z < m ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ (x : ZMod m) + (x : ZMod m) = w ∧ (y : ZMod m) + (y : ZMod m) = w ∧ (z : ZMod m) + (z : ZMod m) = w := by
    rcases Finset.two_lt_card.mp h_contra with ⟨ x, hx, y, hy, hxy ⟩ ; use x, y ; aesop;
  have h_diff : (x - y : ZMod m) + (x - y : ZMod m) = 0 ∧ (x - z : ZMod m) + (x - z : ZMod m) = 0 ∧ (y - z : ZMod m) + (y - z : ZMod m) = 0 := by
    grind;
  have h_diff_ne_zero : (x - y : ZMod m) ≠ 0 ∧ (x - z : ZMod m) ≠ 0 ∧ (y - z : ZMod m) ≠ 0 := by
    simp_all +decide [ sub_eq_iff_eq_add ];
    exact ⟨ by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.1 <| Nat.mod_eq_of_lt ( hBlt x hx ) ▸ Nat.mod_eq_of_lt ( hBlt y hy ) ▸ h, by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.2.1 <| Nat.mod_eq_of_lt ( hBlt x hx ) ▸ Nat.mod_eq_of_lt ( hBlt z hz ) ▸ h, by rw [ ZMod.natCast_eq_natCast_iff ] ; exact fun h => hxz.2.2.1 <| Nat.mod_eq_of_lt ( hBlt y hy ) ▸ Nat.mod_eq_of_lt ( hBlt z hz ) ▸ h ⟩;
  have h_diff_eq : (x - y : ZMod m) = (x - z : ZMod m) := by
    have h_diff_eq : ∀ (u v : ZMod m), u + u = 0 → v + v = 0 → u ≠ 0 → v ≠ 0 → u = v := by
      intros u v hu hv hu_ne hv_ne
      have h_two_torsion : ∀ u : ZMod m, u + u = 0 → u ≠ 0 → u = (m / 2 : ℕ) := by
        intro u hu hu_ne
        have h_two_torsion : 2 * u.val = m := by
          have h_two_torsion : 2 * u.val ≡ 0 [MOD m] := by
            simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, two_mul ];
            cases m <;> aesop;
          obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp h_two_torsion;
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.ModEq ];
          haveI := Fact.mk ( by linarith : 1 < m ) ; exact absurd hk ( by nlinarith [ show u.val < m from u.val_lt ] ) ;
        norm_num [ ← h_two_torsion, Nat.mul_div_cancel_left _ ( by decide : 0 < 2 ) ];
        cases m <;> aesop;
      rw [ h_two_torsion u hu hu_ne, h_two_torsion v hv hv_ne ];
    exact h_diff_eq _ _ h_diff.1 h_diff.2.1 h_diff_ne_zero.1 h_diff_ne_zero.2.1;
  simp_all +decide [ sub_eq_sub_iff_add_eq_add ]

/-
In `ZMod m`, there is at most one nonzero element of order dividing two.
-/
theorem two_torsion_eq (m : ℕ) (u v : ZMod m) (hu : u + u = 0) (hv : v + v = 0)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : u = v := by
  rcases m with ( _ | _ | m ) <;> simp_all +decide [ ← two_mul ];
  · fin_cases u ; fin_cases v ; trivial;
  · have h_eq : 2 * u.val = m + 2 ∧ 2 * v.val = m + 2 := by
      have h_eq : 2 * u.val ≡ 0 [MOD (m + 2)] ∧ 2 * v.val ≡ 0 [MOD (m + 2)] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      have h_eq : u.val < m + 2 ∧ v.val < m + 2 := by
        exact ⟨ u.val_lt, v.val_lt ⟩;
      have h_eq : u.val ≠ 0 ∧ v.val ≠ 0 := by
        exact ⟨ by contrapose! hu0; exact Fin.ext hu0, by contrapose! hv0; exact Fin.ext hv0 ⟩;
      exact ⟨ by obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp ( by tauto : 2 * u.val ≡ 0 [MOD m + 2] ) ; nlinarith [ show k = 1 by nlinarith [ Nat.pos_of_ne_zero h_eq.1 ] ], by obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp ( by tauto : 2 * v.val ≡ 0 [MOD m + 2] ) ; nlinarith [ show k = 1 by nlinarith [ Nat.pos_of_ne_zero h_eq.2 ] ] ⟩;
    exact ZMod.val_injective _ ( by linarith )

/-
`|T1| = |B|`.
-/
theorem fsT1_card (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT1 m B).card = B.card := by
  apply Finset.card_image_of_injOn;
  intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

/-
`|T2| = |B|`.
-/
theorem fsT2_card (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT2 m B).card = B.card := by
  apply Finset.card_image_of_injOn; intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
  exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h

/-
`|T3| = |B| - 1`.
-/
theorem fsT3_card (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT3 m a B).card = B.card - 1 := by
  -- The function x ↦ (x: ZMod m) - (a: ZMod m) is injective on B since B is a subset of {1, ..., m-1}.
  have h_inj : (B.image (fun x : ℕ => (x : ZMod m) - (a : ZMod m))).card = B.card := by
    rw [ Finset.card_image_of_injOn ];
    intro x hx y hy; have := hB.1 x hx; have := hB.1 y hy; simp_all +decide [ sub_eq_iff_eq_add, ZMod.natCast_eq_natCast_iff' ] ;
    exact fun h => Nat.mod_eq_of_lt ( by linarith : x < m ) ▸ Nat.mod_eq_of_lt ( by linarith : y < m ) ▸ h;
  rw [ ← h_inj, fsT3, Finset.card_erase_of_mem ] ; aesop

/-
`|T4| = |B| - 1`.
-/
theorem fsT4_card (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT4 m b B).card = B.card - 1 := by
  erw [ Finset.card_erase_of_mem, Finset.card_image_of_injOn ];
  · intro x hx y hy; simp_all +decide [ sub_eq_sub_iff_add_eq_add, ZMod.natCast_eq_natCast_iff' ] ;
    exact fun h => Nat.mod_eq_of_lt ( hB.1 x hx |>.2 ) ▸ Nat.mod_eq_of_lt ( hB.1 y hy |>.2 ) ▸ h;
  · exact Finset.mem_image.mpr ⟨ b, hbB, by simp +decide ⟩

/-
`|T1 ∩ T2| ≤ 1`.
-/
theorem fsT1T2_le (m : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) :
    (fsT1 m B ∩ fsT2 m B).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_;
  intros a ha b hb
  have h_torsion : a + a = 0 ∧ a ≠ 0 ∧ b + b = 0 ∧ b ≠ 0 := by
    have h_torsion : ∀ x ∈ B, ∀ y ∈ B, (x : ZMod m) = -(y : ZMod m) → x = y ∧ 2 * (x : ZMod m) = 0 ∧ (x : ZMod m) ≠ 0 := by
      intros x hx y hy hxy
      have h_eq : x + y ≡ 0 [MOD m] := by
        simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ]
      have h_ne : x ≠ y → ¬(m ∣ (x + y)) := by
        exact fun h => hB.2 x hx y hy h |>.1
      have h_eq' : x = y := by
        exact Classical.not_not.1 fun h => h_ne h <| Nat.dvd_of_mod_eq_zero h_eq
      have h_torsion : 2 * (x : ZMod m) = 0 := by
        grind
      have h_nonzero : (x : ZMod m) ≠ 0 := by
        rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( hB.1 x hx |>.1 ) ( hB.1 x hx |>.2 )
      exact ⟨h_eq', h_torsion, h_nonzero⟩;
    simp_all +decide [ fsT1, fsT2 ];
    grind;
  exact two_torsion_eq m a b h_torsion.1 h_torsion.2.2.1 h_torsion.2.1 h_torsion.2.2.2

/-
`|T1 ∩ T3| ≤ 1`.
-/
theorem fsT1T3_le (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT1 m B ∩ fsT3 m a B).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_;
  simp +zetaDelta at *;
  intros x hx hx' y hy hy'
  obtain ⟨x', hx', hx''⟩ : ∃ x' ∈ B, (x' : ZMod m) = x := by
    unfold fsT1 at hx; aesop;
  obtain ⟨y', hy', hy''⟩ : ∃ y' ∈ B, (y' : ZMod m) - (a : ZMod m) = x := by
    unfold fsT3 at *; aesop;
  obtain ⟨z', hz', hz''⟩ : ∃ z' ∈ B, (z' : ZMod m) = y := by
    unfold fsT1 at hy; aesop;
  obtain ⟨w', hw', hw''⟩ : ∃ w' ∈ B, (w' : ZMod m) - (a : ZMod m) = y := by
    unfold fsT3 at *; aesop;
  have h_eq : (x' + a) % m = y' ∧ (z' + a) % m = w' := by
    simp_all +decide [ sub_eq_iff_eq_add, ← ZMod.val_natCast ];
    rcases m with ( _ | _ | m ) <;> simp_all +decide [ ZMod.val_natCast ];
    exact ⟨ by rw [ ← hy'', ZMod.val_cast_of_lt ( show y' < m + 1 + 1 from by linarith [ hB.1 y' ‹_› ] ) ], by rw [ ← hw'', ZMod.val_cast_of_lt ( show w' < m + 1 + 1 from by linarith [ hB.1 w' ‹_› ] ) ] ⟩;
  have := hB.2 x' hx' a haB; have := hB.2 z' hz' a haB; simp_all +decide [ Nat.mod_eq_of_lt ] ;

/-
`|T1 ∩ T4| ≤ 2`.
-/
theorem fsT1T4_le (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT1 m B ∩ fsT4 m b B).card ≤ 2 := by
  -- Show that $T1 \cap T4 \subseteq \{ x \in B : x + x \equiv b \pmod{m} \}$.
  have h_subset : fsT1 m B ∩ fsT4 m b B ⊆ (Finset.image (fun x : ℕ => (x : ZMod m)) (B.filter (fun x : ℕ => (x : ZMod m) + (x : ZMod m) = (b : ZMod m)))) := by
    intro x hx; simp_all +decide [ Finset.subset_iff ] ;
    obtain ⟨ a, ha, rfl ⟩ := Finset.mem_image.mp hx.1; use a; simp_all +decide [ fsT4 ] ;
    obtain ⟨ c, hc, h ⟩ := hx.2.2; have := hB.2 a ha c hc; simp_all +decide [ sub_eq_iff_eq_add ] ;
    by_cases hac : a = c <;> simp_all +decide [ ← ZMod.val_natCast ];
    simp_all +decide [ ← h, ZMod.val_natCast ];
    exact False.elim <| this.2 <| by simpa [ Nat.mod_eq_of_lt ( show b < m from hB.1 b hbB |>.2 ) ] using hbB;
  exact le_trans ( Finset.card_le_card h_subset ) ( Finset.card_image_le.trans ( card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) _ ) )

/-
`|T2 ∩ T3| ≤ 2`.
-/
theorem fsT2T3_le (m a : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (haB : a ∈ B) :
    (fsT2 m B ∩ fsT3 m a B).card ≤ 2 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.image ( fun x : ℕ => - ( x : ZMod m ) ) ( B.filter ( fun x : ℕ => ( x : ZMod m ) + ( x : ZMod m ) = ( a : ZMod m ) ) );
  · intro z hz;
    obtain ⟨x, hx, hx'⟩ : ∃ x ∈ B, z = -(x : ZMod m) := by
      unfold fsT2 at hz; aesop;
    obtain ⟨y, hy, hy'⟩ : ∃ y ∈ B, z = (y : ZMod m) - (a : ZMod m) ∧ z ≠ 0 := by
      rw [Finset.mem_inter] at hz
      obtain ⟨_, hz3⟩ := hz
      simp only [fsT3, Finset.mem_erase, Finset.mem_image] at hz3
      obtain ⟨hz_ne, y, hy, hyeq⟩ := hz3
      exact ⟨y, hy, hyeq.symm, hz_ne⟩
    by_cases hxy : x = y;
    · grind +qlia;
    · have h_contradiction : (x + y) % m = a := by
        haveI := Fact.mk ( by linarith : 1 < m ) ; simp_all +decide [ ← ZMod.val_natCast, Nat.add_mod ] ;
        rw [ show ( x + y : ZMod m ) = a by linear_combination' hx' ] ; rw [ ZMod.val_cast_of_lt ] ; linarith [ hB.1 a haB ] ;
      have := hB.2 x hx y hy hxy; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  · refine' le_trans ( Finset.card_image_le ) _;
    convert card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) ( a : ZMod m ) using 1

/-
`|T2 ∩ T4| ≤ 1`.
-/
theorem fsT2T4_le (m b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B) (hbB : b ∈ B) :
    (fsT2 m B ∩ fsT4 m b B).card ≤ 1 := by
  have h_eq : ∀ z ∈ fsT2 m B ∩ fsT4 m b B, z = -(b : ZMod m) := by
    intro z hz
    obtain ⟨x, hx⟩ : ∃ x ∈ B, z = -(x : ZMod m) := by
      unfold fsT2 at hz; aesop;
    obtain ⟨y, hy⟩ : ∃ y ∈ B, z = (b : ZMod m) - (y : ZMod m) := by
      rw [Finset.mem_inter] at hz
      obtain ⟨_, hz4⟩ := hz
      simp only [fsT4, Finset.mem_erase, Finset.mem_image] at hz4
      obtain ⟨_, y, hy, hyeq⟩ := hz4
      exact ⟨y, hy, hyeq.symm⟩
    have hxy : (x + b) % m = y := by
      have hxy : (x + b : ZMod m) = y := by
        grind +ring;
      haveI := Fact.mk ( by linarith : 1 < m ) ; simp_all +decide [ ← ZMod.val_natCast ] ;
      exact ZMod.val_cast_of_lt ( by linarith [ hB.1 y hy.1 ] )
    by_cases hxb : x = b;
    · grind;
    · have := hB.2 x hx.1 b hbB hxb; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  exact Finset.card_le_one.mpr fun x hx y hy => h_eq x hx ▸ h_eq y hy ▸ rfl

/-
`|T3 ∩ T4| ≤ 3`.
-/
theorem fsT3T4_le (m a b : ℕ) (hm : 2 ≤ m) (B : Finset ℕ) (hB : FoldedOK m B)
    (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hnc : a + b ∉ collisions m B) :
    (fsT3 m a B ∩ fsT4 m b B).card ≤ 3 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact { ( b : ZMod m ) - ( a : ZMod m ) } ∪ Finset.image ( fun x : ℕ => ( x : ZMod m ) - ( a : ZMod m ) ) ( Finset.filter ( fun x : ℕ => ( x : ZMod m ) + ( x : ZMod m ) = ( a : ZMod m ) + ( b : ZMod m ) ) B );
  · intro z hz
    simp [fsT3, fsT4] at hz;
    obtain ⟨ ⟨ x, hx, hx' ⟩, hz', ⟨ y, hy, hy' ⟩ ⟩ := hz; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- Since $x + y \equiv a + b \pmod{m}$, we have $x + y = a + b$ or $x + y = a + b + m$.
    have hxy : x + y = a + b ∨ x + y = a + b + m := by
      have hxy : (x + y : ℤ) ≡ (a + b : ℤ) [ZMOD m] := by
        simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        ring;
      obtain ⟨ k, hk ⟩ := hxy.symm.dvd;
      rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> first | left; nlinarith | skip;
      exact Or.inr ( by nlinarith [ show k = 1 by nlinarith [ hB.1 x hx, hB.1 y hy ] ] );
    cases hxy <;> simp_all +decide [ ← eq_sub_iff_add_eq' ];
    · grind;
    · -- Since $x + y = a + b + m$, we have $x = y$.
      have hxy_eq : x = y := by
        contrapose! hnc;
        refine' Finset.mem_inter.mpr ⟨ _, _ ⟩;
        · exact Finset.mem_image.mpr ⟨ ( a, b ), Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ haB, hbB ⟩, by linarith, by linarith ⟩, by ring ⟩;
        · refine' Finset.mem_image.mpr ⟨ ( if x < y then ( x, y ) else ( y, x ) ), _, _ ⟩ <;> split_ifs <;> simp_all +decide [ add_comm ];
          · exact Or.inr ( by linarith );
          · exact ⟨ lt_of_le_of_ne ‹_› ( Ne.symm hnc ), Or.inl ( by linarith [ hB.1 a haB ] ) ⟩;
      grind;
  · refine' le_trans ( Finset.card_union_le _ _ ) _;
    refine' le_trans ( add_le_add ( Finset.card_singleton _ |> le_of_eq ) ( Finset.card_image_le ) ) _;
    have := card_two_mul_fiber_le m hm B ( fun x hx => by linarith [ hB.1 x hx ] ) ( a + b : ZMod m ) ; simp_all +decide [ ← two_mul ] ;
    linarith

/-
**Case 2 (four-set bound).** If the two smallest elements `a < b` of `B` have
`a + b < m` and `a + b` is *not* a collision, then `|B| ≤ m/4 + 3`.
-/
theorem four_set_bound (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hnc : a + b ∉ collisions m B) :
    (B.card : ℝ) ≤ (m : ℝ) / 4 + 3 := by
  rw [ div_add', le_div_iff₀ ] <;> norm_cast;
  have h_four_set : (fsT1 m B).card + (fsT2 m B).card + (fsT3 m a B).card + (fsT4 m b B).card ≤ m + 10 := by
    -- By the four-set bound, we have:
    have h_four_set_bound : (fsT1 m B ∪ fsT2 m B ∪ fsT3 m a B ∪ fsT4 m b B).card ≤ m := by
      cases m <;> [ aesop; exact le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ];
    have := card_sum_le_union_add_pairwise ( fsT1 m B ) ( fsT2 m B ) ( fsT3 m a B ) ( fsT4 m b B );
    linarith [ fsT1T2_le m hm B hB, fsT1T3_le m a hm B hB haB, fsT1T4_le m b hm B hB hbB, fsT2T3_le m a hm B hB haB, fsT2T4_le m b hm B hB hbB, fsT3T4_le m a b hm B hB haB hbB hab hmin h2nd hlt hnc ];
  linarith [ fsT1_card m hm B hB, fsT2_card m hm B hB, fsT3_card m a hm B hB haB, fsT4_card m b hm B hB hbB, Nat.sub_add_cancel ( show 1 ≤ B.card from Finset.card_pos.mpr ⟨ a, haB ⟩ ) ]

/-
**Case 1 (deletion step).** If the two smallest elements `a < b` of `B` have
`a + b < m` and `a + b` *is* a collision, then deleting `a` strictly decreases the number of
collisions.
-/
theorem collisions_erase_lt (m : ℕ) (B : Finset ℕ) (hB : FoldedOK m B)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x)
    (hlt : a + b < m) (hc : a + b ∈ collisions m B) :
    (collisions m (B.erase a)).card < (collisions m B).card := by
  refine' Finset.card_lt_card _;
  constructor;
  · exact Finset.inter_subset_inter ( Finset.image_subset_image <| Finset.filter_subset_filter _ <| Finset.product_subset_product ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) ) ( Finset.image_subset_image <| Finset.filter_subset_filter _ <| Finset.product_subset_product ( Finset.erase_subset _ _ ) ( Finset.erase_subset _ _ ) );
  · simp_all +decide [ Finset.subset_iff, collisions ];
    use a + b; simp_all +decide [ lowSums, highSums ] ;
    grind

/-
One induction step: given the two smallest elements `a < b` with `a + b < m` and the
induction hypothesis for all strictly smaller sets (same `m`), the bound holds for `B`.
-/
theorem lemma1_step (m : ℕ) (B : Finset ℕ) (hm : 2 ≤ m) (hB : FoldedOK m B)
    (IH : ∀ B' : Finset ℕ, B'.card < B.card → FoldedOK m B' →
          (B'.card : ℝ) - (collisions m B').card ≤ (m : ℝ) / 4 + 3)
    (a b : ℕ) (haB : a ∈ B) (hbB : b ∈ B) (hab : a < b)
    (hmin : ∀ x ∈ B, a ≤ x) (h2nd : ∀ x ∈ B, x ≠ a → b ≤ x) (hlt : a + b < m) :
    (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + 3 := by
  by_cases h : a + b ∈ collisions m B;
  · have := IH ( B.erase a ) ?_ ?_;
    · rw [ Finset.card_erase_of_mem haB ] at this;
      rw [ Nat.cast_pred ( Finset.card_pos.mpr ⟨ a, haB ⟩ ) ] at this;
      linarith [ show ( collisions m B |> Finset.card : ℝ ) ≥ ( collisions m ( B.erase a ) |> Finset.card : ℝ ) + 1 by exact_mod_cast collisions_erase_lt m B hB a b haB hbB hab hmin h2nd hlt h ];
    · exact Finset.card_lt_card ( Finset.erase_ssubset haB );
    · exact FoldedOK_erase m B a hB;
  · exact le_trans ( sub_le_self _ <| Nat.cast_nonneg _ ) ( four_set_bound m B hm hB a b haB hbB hab hmin h2nd hlt h )

/-
**Lemma 1.** There is an absolute constant `K₁` such that for every `m ≥ 2` and every
`B` satisfying `FoldedOK m B`, one has `|B| − |C(B)| ≤ m/4 + K₁`.
-/
theorem lemma1 :
    ∃ K1 : ℝ, ∀ (m : ℕ) (B : Finset ℕ), 2 ≤ m → FoldedOK m B →
      (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + K1 := by
  use 3;
  have h_ind : ∀ n : ℕ, ∀ m : ℕ, 2 ≤ m → ∀ B : Finset ℕ, B.card = n → FoldedOK m B → (B.card : ℝ) - (collisions m B).card ≤ (m : ℝ) / 4 + 3 := by
    intro n;
    induction' n using Nat.strong_induction_on with n ih;
    intro m hm B hB_card hB_foldedOK
    by_cases hB_card_le_1 : B.card ≤ 1;
    · interval_cases _ : #B <;> norm_num at *;
      · exact le_trans ( neg_nonpos_of_nonneg ( Nat.cast_nonneg _ ) ) ( by positivity );
      · grind +qlia;
    · obtain ⟨a, b, haB, hbB, hab, hmin, h2nd⟩ : ∃ a b : ℕ, a ∈ B ∧ b ∈ B ∧ a < b ∧ (∀ x ∈ B, a ≤ x) ∧ (∀ x ∈ B, x ≠ a → b ≤ x) := by
        obtain ⟨a, haB⟩ : ∃ a : ℕ, a ∈ B ∧ ∀ x ∈ B, a ≤ x := by
          exact ⟨ Nat.find <| Finset.card_pos.mp <| by linarith, Nat.find_spec <| Finset.card_pos.mp <| by linarith, fun x hx => Nat.find_min' _ hx ⟩;
        obtain ⟨b, hbB, hb_min⟩ : ∃ b : ℕ, b ∈ B ∧ b ≠ a ∧ ∀ x ∈ B, x ≠ a → b ≤ x := by
          exact ⟨ Nat.find ( Finset.exists_mem_ne ( by linarith ) a ), Nat.find_spec ( Finset.exists_mem_ne ( by linarith ) a ) |>.1, Nat.find_spec ( Finset.exists_mem_ne ( by linarith ) a ) |>.2, fun x hx hx' => Nat.find_min' ( Finset.exists_mem_ne ( by linarith ) a ) ⟨ hx, hx' ⟩ ⟩;
        exact ⟨ a, b, haB.1, hbB, lt_of_le_of_ne ( haB.2 b hbB ) ( Ne.symm hb_min.1 ), haB.2, hb_min.2 ⟩;
      by_cases hlt : a + b < m;
      · apply lemma1_step m B hm hB_foldedOK (fun B' hB'_card hB'_foldedOK => ih B'.card (by
        linarith) m hm B' rfl hB'_foldedOK) a b haB hbB hab hmin h2nd hlt;
      · -- Let $u := B.max'$ and $v := (B.erase u).max'$ (the two largest of $B$), so $v < u$, $u,v \in B$.
        obtain ⟨u, huB, hu_max⟩ : ∃ u ∈ B, ∀ x ∈ B, x ≤ u := by
          exact ⟨ Finset.max' B ⟨ a, haB ⟩, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩
        obtain ⟨v, hvB, hv_max⟩ : ∃ v ∈ B, v ≠ u ∧ ∀ x ∈ B, x ≠ u → x ≤ v := by
          obtain ⟨v, hvB, hv_max⟩ : ∃ v ∈ B, v ≠ u := by
            exact Finset.exists_mem_ne ( by linarith ) u;
          exact ⟨ Finset.max' ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( B.filter fun x => x ≠ u ) ⟨ v, by aesop ⟩ ) |>.2, fun x hx hx' => Finset.le_max' _ _ ( by aesop ) ⟩
        have hv_lt_u : v < u := by
          exact lt_of_le_of_ne ( hu_max v hvB ) hv_max.1
        have hu_v_ge_m : u + v ≥ m := by
          grind
        have hu_v_ne_m : u + v ≠ m := by
          intro h; have := hB_foldedOK.2 u huB v hvB; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        have hu_v_gt_m : u + v > m := by
          exact lt_of_le_of_ne hu_v_ge_m hu_v_ne_m.symm;
        -- The two smallest elements of $B'$ are $a' := m - u$ and $b' := m - v$, with $a' < b'$ (since $v < u$), $a', b' \in B'$.
        set a' := m - u
        set b' := m - v
        have ha'_B' : a' ∈ negSet m B := by
          exact Finset.mem_image.mpr ⟨ u, huB, rfl ⟩
        have hb'_B' : b' ∈ negSet m B := by
          exact Finset.mem_image.mpr ⟨ v, hvB, rfl ⟩
        have ha'_lt_b' : a' < b' := by
          exact Nat.sub_lt_sub_left ( by linarith [ hB_foldedOK.1 u huB, hB_foldedOK.1 v hvB ] ) hv_lt_u
        have ha'_min : ∀ x ∈ negSet m B, a' ≤ x := by
          simp +zetaDelta at *;
          intro x hx; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; linarith [ hu_max y hy, Nat.sub_add_cancel ( show y ≤ m from by linarith [ hB_foldedOK.1 y hy ] ) ] ;
        have hb'_2nd : ∀ x ∈ negSet m B, x ≠ a' → b' ≤ x := by
          intros x hx hx_ne_a'
          obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, x = m - y := by
            unfold negSet at hx; aesop;
          grind
        have ha'_b'_lt_m : a' + b' < m := by
          rw [ tsub_add_tsub_comm ] <;> try linarith [ hB_foldedOK.1 u huB, hB_foldedOK.1 v hvB ];
          lia;
        -- Apply `lemma1_step` to $B'$.
        have hB'_step : (negSet m B).card - (collisions m (negSet m B)).card ≤ (m : ℝ) / 4 + 3 := by
          apply lemma1_step m (negSet m B) hm (negSet_foldedOK m B hm hB_foldedOK) (fun B' hB'_card hB'_foldedOK => by
            convert ih _ _ _ hm _ rfl hB'_foldedOK using 1;
            exact hB'_card.trans_le ( by rw [ negSet_card m B hB_foldedOK ] ; linarith )) a' b' ha'_B' hb'_B' ha'_lt_b' ha'_min hb'_2nd ha'_b'_lt_m;
        convert hB'_step using 1;
        rw [ negSet_card m B hB_foldedOK, negSet_collisions_card m B hm hB_foldedOK ];
  exact fun m B hm hB => h_ind _ _ hm _ rfl hB


-- ============================================================
-- Main
-- ============================================================

set_option maxHeartbeats 4000000

open scoped BigOperators
open Finset


/-!
# Erdős problem 865 — conditional proof of the `5/8` upper bound

This file formalizes the user's argument that every *bad* set `A ⊆ {1,…,N}` has
`|A| ≤ (5/8) N + O(1)`, **conditional on** the external "coarse theorem"
`CoarseBound θ K₀` for some `θ < 2/3`.

The logical chain is:

* `lemma1`  : the folded additive lemma, `|B| − |C(B)| ≤ m/4 + O(1)`.
* `lemma2`  : folding a bad set around a pivot, `|X| + |Y| ≤ (5/4)h − |I| + O(1)`.
* `badset_even` : the `5/4 H` bound for bad subsets of `{1,…,2H}` (uses `lemma2` + coarse).
* `badset_card_le` : the `5/8 N` bound for all `N` (reduces odd `N` to even).
* `conditional_threshold` : the threshold statement (existence of a triple once `|A| ≥ (5/8)N + C`).
* `sharp`   : the matching construction, showing the constant `5/8` is best possible.
-/

/-- The external "coarse theorem": every bad `S ⊆ {1,…,M}` has `|S| ≤ θ M + K₀`. -/
def CoarseBound (θ K0 : ℝ) : Prop :=
  ∀ (M : ℕ) (S : Finset ℕ), MemRange M S → IsBad S → (S.card : ℝ) ≤ θ * M + K0

/-! ## Helper lemmas for Lemma 2 -/

/-
The folded set `B = X ∩ Y` satisfies the hypothesis `FoldedOK h B` of Lemma 1.
-/
theorem Bset_foldedOK (h : ℕ) (A : Finset ℕ) (hbad : IsBad A)
    (hh : h ∈ A) (hh1 : 1 ≤ h) : FoldedOK h (Bset h A) := by
  refine' ⟨ _, _ ⟩;
  · exact fun x hx => ⟨ Finset.mem_Ico.mp ( Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 ) |>.1, Finset.mem_Ico.mp ( Finset.mem_filter.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1 ) |>.2 ⟩;
  · intro x hx y hy hxy
    by_contra h_contra
    have h_triple : x + y ∈ A := by
      unfold Bset at *; simp_all +decide [ Finset.mem_inter ] ;
      unfold Xset Yset at *; simp_all +decide [ Finset.mem_filter, Finset.mem_Ico ] ;
      by_cases h_div : h ∣ x + y <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      · have := Nat.dvd_of_mod_eq_zero h_div; obtain ⟨ k, hk ⟩ := this; rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        grind;
      · -- Since $x + y \equiv r \pmod{h}$ and $r \in A$, we have $x + y = r + kh$ for some integer $k$.
        obtain ⟨k, hk⟩ : ∃ k : ℕ, x + y = (x + y) % h + k * h := by
          exact ⟨ ( x + y ) / h, by rw [ Nat.mod_add_div' ] ⟩;
        rcases k with ( _ | _ | k ) <;> norm_num at *;
        · grind;
        · grind +splitIndPred;
        · grind +splitIndPred;
    refine' hbad _;
    use x, ?_, y, ?_, h, ?_ <;> simp_all +decide [ Bset, Xset, Yset ];
    lia

/-
Every collision residue lies in the excluded set `E`.
-/
theorem collisions_subset_Eset (h : ℕ) (A : Finset ℕ) (hbad : IsBad A)
    (hh : h ∈ A) : collisions h (Bset h A) ⊆ Eset h A := by
  intro x hx
  simp [collisions, lowSums, highSums, Eset] at hx ⊢
  rcases hx with ⟨ ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, hlt ⟩, rfl ⟩, ⟨ c, d, ⟨ ⟨ hc, hd ⟩, hcd, hlt' ⟩, hcd' ⟩ ⟩ ; simp_all +decide [ Bset, Xset, Yset ] ;
  refine' ⟨ by linarith, _, _ ⟩ <;> intro <;> contrapose! hbad <;> simp_all +decide [ IsBad ];
  · use a, ha.1.2, b, hb.1.2, h, hh;
    grind;
  · use c, hc.1.2, d, hd.1.2, h, hh;
    grind

/-
The basic counting identity `|X| + |Y| + |E| = |{1,…,h-1}| + |B|`.
-/
theorem card_XY_identity (h : ℕ) (A : Finset ℕ) :
    (Xset h A).card + (Yset h A).card + (Eset h A).card
      = (Finset.Ico 1 h).card + (Bset h A).card := by
  unfold Xset Yset Bset Eset;
  rw [ Finset.card_sdiff ];
  rw [ show ( Xset h A ∪ Yset h A ) ∩ Finset.Ico 1 h = ( Xset h A ∪ Yset h A ) from ?_ ];
  · zify [ Xset, Yset ];
    rw [ Nat.cast_sub ];
    · grind;
    · exact Finset.card_le_card ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) );
  · exact Finset.inter_eq_left.mpr ( Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.filter_subset _ _ ) )

/-! ## Lemma 2 : folding a bad set around a pivot -/

/-
**Lemma 2.** There is an absolute constant `K₂` such that for every bad `A ⊆ {1,…,N}`,
every pivot `h ∈ A`, and every `I ⊆ E ∖ C(B)`, one has
`|X| + |Y| ≤ (5/4)h − |I| + K₂`.
-/
theorem lemma2 :
    ∃ K2 : ℝ, ∀ (N h : ℕ) (A : Finset ℕ), MemRange N A → IsBad A → h ∈ A → 1 ≤ h →
      ∀ I : Finset ℕ, I ⊆ (Eset h A) \ (collisions h (Bset h A)) →
        ((Xset h A).card + (Yset h A).card : ℝ) ≤ 5 / 4 * h - I.card + K2 := by
  -- Let's choose K2 as the maximum of the constants from lemma1 and 0, plus 2.
  use max (Classical.choose (lemma1)) 0 + 2;
  intro N h A hA hbad hh hh1 I hI;
  by_cases hh2 : 2 ≤ h;
  · have := Classical.choose_spec ( lemma1 ) h ( Bset h A ) hh2 ( Bset_foldedOK h A hbad hh hh1 );
    -- Using the identity from `card_XY_identity`, we can rewrite the goal in terms of `B` and `E`.
    have h_identity : ((Xset h A).card : ℝ) + ((Yset h A).card : ℝ) = (h - 1 : ℝ) + (Bset h A).card - (Eset h A).card := by
      have h_identity : ((Xset h A).card : ℝ) + ((Yset h A).card : ℝ) + ((Eset h A).card : ℝ) = (h - 1 : ℝ) + (Bset h A).card := by
        have := card_XY_identity h A; norm_cast at *; aesop;
      linarith;
    -- Using the fact that $E \geq I + C$, we can substitute this into the identity.
    have h_E_ge_I_C : (Eset h A).card ≥ (I.card : ℝ) + (collisions h (Bset h A)).card := by
      norm_cast;
      rw [ ← Finset.card_union_of_disjoint ];
      · exact Finset.card_le_card ( Finset.union_subset ( hI.trans ( Finset.sdiff_subset ) ) ( collisions_subset_Eset h A hbad hh ) );
      · exact Finset.disjoint_left.mpr fun x hxI hx => Finset.mem_sdiff.mp ( hI hxI ) |>.2 hx;
    grind;
  · interval_cases h ; norm_num [ Xset, Yset, Eset ] at *;
    norm_num [ hI ] ; positivity

/-! ## The even case -/

/-
Counting helper: every element of a bad set `A ⊆ {1,…,2H}` is counted by `X` (if `< h`),
is the pivot `h`, is counted by `Y` (if `h < · < 2h`), or lies in the tail `· ≥ 2h`.
-/
theorem card_le_XY_tail (H h : ℕ) (A : Finset ℕ) (hA : MemRange (2 * H) A) (hh1 : 1 ≤ h) :
    A.card ≤ (Xset h A).card + (Yset h A).card + (A.filter (fun a => 2 * h ≤ a)).card + 1 := by
  -- Let's simplify the goal using the definitions of `Xset`, `Yset`, and `Eset`.
  suffices h_suff : A ⊆ (Xset h A) ∪ (Yset h A).image (fun r => h + r) ∪ {h} ∪ (A.filter (fun a => 2 * h ≤ a)) by
    refine le_trans ( Finset.card_le_card h_suff ) ?_;
    grind;
  intro x hx; by_cases hx' : x < h <;> by_cases hx'' : x = h <;> simp_all +decide [ Xset, Yset ] ;
  · exact Or.inl ( hA x hx |>.1 );
  · exact if h'' : x < 2 * h then Or.inr <| Or.inl ⟨ x - h, ⟨ ⟨ by omega, by omega ⟩, by convert hx using 1; omega ⟩, by omega ⟩ else Or.inr <| Or.inr <| by omega;

/-
Combined counting bound: folding a bad set around a pivot `h`, with an excluded set `I`
and the tail of elements `≥ 2h`, gives `|A| ≤ (5/4)h + |tail| − |I| + O(1)`.
-/
theorem pivot_bound :
    ∃ K : ℝ, ∀ (H h : ℕ) (A : Finset ℕ), MemRange (2 * H) A → IsBad A → h ∈ A → 1 ≤ h →
      ∀ I : Finset ℕ, I ⊆ (Eset h A) \ (collisions h (Bset h A)) →
        (A.card : ℝ) ≤ 5 / 4 * h + (A.filter (fun a => 2 * h ≤ a)).card - I.card + K := by
  obtain ⟨ K2, hK2 ⟩ := lemma2;
  use K2 + 1;
  intro H h A hA hbad hh hh1 I hI; linarith [ hK2 ( 2 * H ) h A hA hbad hh hh1 I hI, show ( A.card : ℝ ) ≤ ( Xset h A ).card + ( Yset h A ).card + ( A.filter fun a => 2 * h ≤ a ).card + 1 from mod_cast card_le_XY_tail H h A hA hh1 ] ;

/-
**Case 1** (`s ≤ 4e`): fold around `q = H + s`.  No use of the coarse theorem.
-/
theorem badset_case1 :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ) (p q : ℕ),
      MemRange (2 * H) A → IsBad A → 1 ≤ p → p ≤ H → H ≤ q → q ≤ 2 * H →
      p ∈ A → q ∈ A → (∀ x ∈ A, x ≤ p ∨ q ≤ x) → q - H ≤ 4 * (H - p) →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  by_contra h_contra;
  -- Apply `pivot_bound` to obtain a contradiction.
  obtain ⟨K, hK⟩ := pivot_bound;
  refine' h_contra ⟨ K + 2, fun H A p q hA hbad hp1 hpH hHq hq2H hpA hqA hgap hcase => _ ⟩;
  -- Let $I := \text{Finset.Ioo}(H - \min(e, s), q)$.
  set e := H - p
  set s := q - H
  set m0 := min e s
  set I := Finset.Ioo (H - m0) q;
  -- CLAIM A: I ⊆ Eset q A \ collisions q (Bset q A).
  have hI_subset : I ⊆ Eset q A \ collisions q (Bset q A) := by
    intro r hr; simp_all +decide [ Eset, collisions ] ;
    refine' ⟨ ⟨ ⟨ _, _ ⟩, _, _ ⟩, _ ⟩;
    · grind;
    · exact Finset.mem_Ioo.mp hr |>.2;
    · simp +zetaDelta at *;
      exact fun h => by have := hgap r ( Finset.mem_filter.mp h |>.2 ) ; omega;
    · simp +zetaDelta at *;
      exact fun h => by have := hA _ ( Finset.mem_filter.mp h |>.2 ) ; omega;
    · intro hr₁ hr₂; simp_all +decide [ lowSums, highSums ] ;
      obtain ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, h ⟩, rfl ⟩ := hr₁; obtain ⟨ c, d, ⟨ ⟨ hc, hd ⟩, hcd, h' ⟩, h'' ⟩ := hr₂; simp_all +decide [ Bset, Xset, Yset ] ;
      grind;
  -- CLAIM B: (I.card : ℝ) ≥ (s:ℝ) + m0 - 1.
  have hI_card : (I.card : ℝ) ≥ (s : ℝ) + m0 - 1 := by
    simp +zetaDelta at *;
    norm_cast;
    omega;
  -- CLAIM C: (A.filter (fun a => 2*q ≤ a)).card ≤ 1.
  have h_filter_card : (A.filter (fun a => 2 * q ≤ a)).card ≤ 1 := by
    exact Finset.card_le_one.mpr fun x hx y hy => by linarith [ Finset.mem_filter.mp hx, Finset.mem_filter.mp hy, hA x ( Finset.mem_filter.mp hx |>.1 ), hA y ( Finset.mem_filter.mp hy |>.1 ) ] ;
  -- Apply `pivot_bound` with `h = q`.
  have h_pivot : (A.card : ℝ) ≤ 5 / 4 * q + (A.filter (fun a => 2 * q ≤ a)).card - I.card + K := by
    grind;
  -- Since $m0 = \min(e, s)$, we have $(1/4)*s - m0 \leq 0$.
  have h_min : (1 / 4 : ℝ) * s - m0 ≤ 0 := by
    cases min_cases e s <;> simp +decide [ * ];
    · rw [ inv_mul_le_iff₀ ] <;> norm_cast;
      grind;
    · grind +splitImp;
  linarith [ show ( q : ℝ ) = H + s by rw [ Nat.cast_sub ] <;> linarith, show ( Finset.card ( Finset.filter ( fun a => 2 * q ≤ a ) A ) : ℝ ) ≤ 1 by exact_mod_cast h_filter_card ]

/-
**Case 2** (`s > 4e`): fold around `p = H − e`; uses the coarse theorem.
-/
theorem badset_case2 {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ) (p q : ℕ),
      MemRange (2 * H) A → IsBad A → 1 ≤ p → p ≤ H → H ≤ q → q ≤ 2 * H →
      p ∈ A → q ∈ A → (∀ x ∈ A, x ≤ p ∨ q ≤ x) → 4 * (H - p) < q - H →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  -- Apply `pivot_bound` to obtain the constant `K`.
  obtain ⟨K, hK⟩ := pivot_bound;
  use K0 + K + 3;
  intro H A p q hA hbad hp1 hpH hHq hq2H hpA hqA hgap hcase;
  let e := H - p;
  let s := q - H;
  have he : p = H - e := by
    rw [ Nat.sub_sub_self hpH ];
  have hs : q = H + s := by
    rw [ Nat.add_sub_of_le hHq ];
  have h4e : 4 * e < s := by
    exact hcase;
  have hs_le_H : s ≤ H := by
    omega;
  have ht : 1 ≤ p := by
    grind;
  obtain ⟨I, hI⟩ : ∃ I : Finset ℕ, I ⊆ (Eset p A) \ (collisions p (Bset p A)) ∧ (I.card : ℝ) ≥ (1 - θ) * (min (s + e - 1) (p - 1)) - K0 := by
    refine' ⟨ Finset.Icc 1 ( Min.min ( s + e - 1 ) ( p - 1 ) ) \ A, _, _ ⟩;
    · intro x hx; simp +decide [ Eset, Bset ] at hx ⊢;
      refine' ⟨ ⟨ ⟨ hx.1.1, lt_of_le_of_lt hx.1.2.2 ( Nat.pred_lt ( ne_bot_of_gt ht ) ) ⟩, _, _ ⟩, _ ⟩ <;> simp +decide [ Xset, Yset, collisions ] at hx ⊢;
      · exact fun _ _ => hx.2;
      · grind +extAll;
      · intro hx' hx''; simp +decide [ lowSums, highSums ] at hx' hx'';
        grind +qlia;
    · have hI_card : (Finset.Icc 1 (min (s + e - 1) (p - 1)) ∩ A).card ≤ θ * (min (s + e - 1) (p - 1)) + K0 := by
        convert hc ( Min.min ( s + e - 1 ) ( p - 1 ) ) ( Finset.Icc 1 ( Min.min ( s + e - 1 ) ( p - 1 ) ) ∩ A ) _ _ using 1;
        · exact fun x hx => ⟨ Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.1 ) |>.1, Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.1 ) |>.2 ⟩;
        · intro h;
          obtain ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, ha', hb', hc' ⟩ := h;
          exact hbad ⟨ a, by simp +decide at ha; tauto, b, by simp +decide at hb; tauto, c, by simp +decide at hc; tauto, hab, hac, hbc, by simp +decide at ha'; tauto, by simp +decide at hb'; tauto, by simp +decide at hc'; tauto ⟩;
      rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · norm_num [ Finset.inter_comm ] at * ; linarith;
      · exact Finset.card_le_card fun x hx => by simpa using Finset.mem_inter.mp hx |>.2;
  -- Apply `pivot_bound` with `h = p` and `I` as chosen.
  have h_pivot : (A.card : ℝ) ≤ 5 / 4 * p + (A.filter (fun a => 2 * p ≤ a)).card - I.card + K := by
    exact hK H p A hA hbad hpA ht I hI.1;
  -- Bound the tail: $(A.filter (fun a => 2 * p ≤ a)).card ≤ 2 * e + 1$.
  have h_tail : (A.filter (fun a => 2 * p ≤ a)).card ≤ 2 * e + 1 := by
    have h_tail : (A.filter (fun a => 2 * p ≤ a)).card ≤ (Finset.Icc (2 * p) (2 * H)).card := by
      exact Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_filter.mp hx ], by linarith [ Finset.mem_filter.mp hx, hA x ( Finset.mem_filter.mp hx |>.1 ) ] ⟩;
    exact h_tail.trans ( by norm_num; omega );
  -- Bound the term $(3/4)*e - (1-θ)*t$.
  have h_bound : (3 / 4 : ℝ) * e - (1 - θ) * (min (s + e - 1) (p - 1)) ≤ 2 := by
    rcases le_total ( s + e - 1 ) ( p - 1 ) with h | h <;> norm_num [ h ];
    · rw [ Nat.cast_sub ];
      · rw [ Nat.cast_sub ] <;> push_cast;
        · rw [ Nat.cast_sub ];
          · nlinarith only [ show ( q : ℝ ) ≥ H + 4 * ( H - p ) + 1 by exact_mod_cast by omega, hθ, show ( p : ℝ ) ≤ H by exact_mod_cast hpH ];
          · grind +qlia;
        · omega;
      · grind +qlia;
    · rw [ Nat.cast_sub ];
      · rw [ Nat.cast_sub ] <;> norm_num;
        · nlinarith only [ show ( p : ℝ ) ≥ 1 by norm_cast, show ( H : ℝ ) ≥ p by norm_cast, hθ, show ( p : ℝ ) ≤ H by norm_cast, show ( q : ℝ ) ≥ H by norm_cast, show ( s : ℝ ) ≤ H by norm_cast, show ( e : ℝ ) = H - p by exact eq_sub_of_add_eq <| by norm_cast; omega, show ( s : ℝ ) ≥ 4 * e + 1 by norm_cast ];
        · linarith;
      · linarith;
  rw [ he ] at *;
  rw [ Nat.cast_sub ( by omega ) ] at *;
  rw [ Nat.cast_sub ( by omega ) ] at *;
  linarith [ show ( Finset.card ( Finset.filter ( fun a => 2 * ( H - ( H - p ) ) ≤ a ) A ) : ℝ ) ≤ 2 * ( H - p ) + 1 by exact_mod_cast h_tail ]

/-
**Even case.** Conditional on the coarse theorem, every bad `A ⊆ {1,…,2H}` has
`|A| ≤ (5/4)H + O(1)`.
-/
theorem badset_even {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (H : ℕ) (A : Finset ℕ), MemRange (2 * H) A → IsBad A →
      (A.card : ℝ) ≤ 5 / 4 * H + C := by
  -- Set $C$ to be the maximum of the constants from `badset_case1` and `badset_case2$ (and ensure it is at least zero).
  obtain ⟨C1, hC1⟩ := badset_case1
  obtain ⟨C2, hC2⟩ := badset_case2 hθ hc
  use max (max C1 C2) 0;
  intro H A hA hbad;
  by_cases hL1 : A.filter (fun x => x ≤ H) = ∅;
  · -- Since $Llow$ is empty, all elements of $A$ are greater than $H$, so $A \subseteq \{H+1, \ldots, 2H\}$.
    have hA_subset : A ⊆ Finset.Icc (H + 1) (2 * H) := by
      exact fun x hx => Finset.mem_Icc.mpr ⟨ Nat.succ_le_of_lt ( lt_of_not_ge fun hx' => Finset.notMem_empty x <| hL1 ▸ Finset.mem_filter.mpr ⟨ hx, hx' ⟩ ), hA x hx |>.2 ⟩;
    have := Finset.card_le_card hA_subset; norm_num at *;
    exact le_trans ( Nat.cast_le.mpr this ) ( by rw [ Nat.cast_sub ( by linarith ) ] ; push_cast; linarith [ le_max_left ( max C1 C2 ) 0, le_max_right ( max C1 C2 ) 0, le_max_left C1 C2, le_max_right C1 C2 ] );
  · by_cases hL2 : A.filter (fun x => H ≤ x) = ∅;
    · simp_all +decide [ Finset.ext_iff ];
      exact le_add_of_le_of_nonneg ( by rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast ; linarith [ show A.card ≤ H from le_trans ( Finset.card_le_card ( show A ⊆ Finset.Ico 1 H from fun x hx => Finset.mem_Ico.mpr ⟨ by linarith [ hA x hx ], hL2 x hx ⟩ ) ) ( by simp ) ] ) ( by positivity );
    · -- Set $p := Llow.max' (nonempty)$ and $q := Lhigh.min' (nonempty)$.
      obtain ⟨p, hp⟩ : ∃ p ∈ A, p ≤ H ∧ ∀ x ∈ A, x ≤ H → x ≤ p := by
        exact ⟨ Finset.max' ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ), Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ) ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.filter ( fun x => x ≤ H ) A ) ( Finset.nonempty_of_ne_empty hL1 ) ) |>.2, fun x hx hx' => Finset.le_max' _ _ ( by aesop ) ⟩
      obtain ⟨q, hq⟩ : ∃ q ∈ A, H ≤ q ∧ ∀ x ∈ A, H ≤ x → q ≤ x := by
        exact ⟨ Finset.min' ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ), Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ) ) |>.1, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.filter ( fun x => H ≤ x ) A ) ( Finset.nonempty_of_ne_empty hL2 ) ) |>.2, fun x hx hx' => Finset.min'_le _ _ ( by aesop ) ⟩;
      by_cases h_case : q - H ≤ 4 * (H - p);
      · refine le_trans ( hC1 H A p q hA hbad ?_ ?_ ?_ ?_ hp.1 hq.1 ?_ h_case ) ?_;
        any_goals linarith [ hA p hp.1, hA q hq.1 ];
        · grind;
        · grind;
      · refine le_trans ( hC2 H A p q hA hbad ?_ ?_ ?_ ?_ hp.1 hq.1 ?_ ?_ ) ?_;
        any_goals linarith [ hA p hp.1, hA q hq.1 ];
        · grind;
        · grind

/-! ## Reduction to general `N` -/

/-
The `5/8 N` bound for all `N`, obtained from the even case by embedding `{1,…,N}` into
`{1,…,2H}` with `N ≤ 2H ≤ N+1`.
-/
theorem badset_card_le {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), MemRange N A → IsBad A →
      (A.card : ℝ) ≤ 5 / 8 * N + C := by
  obtain ⟨ C, hC ⟩ := badset_even hθ hc;
  use C + 5 / 8;
  intro N A hA hA'; specialize hC ( ( N + 1 ) / 2 ) A;
  exact le_trans ( hC ( fun x hx => hA x hx |> fun h => ⟨ h.1, by linarith [ Nat.div_add_mod ( N + 1 ) 2, Nat.mod_lt ( N + 1 ) two_pos, h.2 ] ⟩ ) hA' ) ( by linarith [ show ( ( N + 1 ) / 2 : ℕ ) ≤ ( N : ℝ ) / 2 + 1 / 2 by rw [ div_add_div, le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self ( N + 1 ) 2 ] ] )

/-
**Erdős 865 (conditional threshold form).** Conditional on the coarse theorem, there is
a constant `C` such that every `A ⊆ {1,…,N}` with `|A| ≥ (5/8)N + C` contains an admissible
triple.
-/
theorem conditional_threshold {θ K0 : ℝ} (hθ : θ < 2 / 3) (hc : CoarseBound θ K0) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), MemRange N A →
      (5 / 8 * N + C ≤ (A.card : ℝ)) → HasTriple A := by
  by_contra! h_contra;
  obtain ⟨ C, hC ⟩ := badset_card_le hθ hc;
  exact absurd ( h_contra ( C + 1 ) ) ( by rintro ⟨ N, A, hA₁, hA₂, hA₃ ⟩ ; linarith [ hC N A hA₁ ( by unfold IsBad; aesop ) ] )

/-! ## Sharpness of the constant `5/8` -/

/-
**Sharpness.** For `N = 8k` (`k ≥ 1`), the set `[k,2k] ∪ [4k,8k] ⊆ {1,…,N}` is bad and
has `5k + 2 = (5/8)N + 2` elements.  Hence the constant `5/8` is best possible.
-/
theorem sharp (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : Finset ℕ, MemRange (8 * k) A ∧ IsBad A ∧ A.card = 5 * k + 2 := by
  refine' ⟨ Finset.Icc k ( 2 * k ) ∪ Finset.Icc ( 4 * k ) ( 8 * k ), _, _, _ ⟩;
  · exact fun x hx => by rcases Finset.mem_union.mp hx with ( hx | hx ) <;> constructor <;> linarith [ Finset.mem_Icc.mp hx ] ;
  · rintro ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, h₁, h₂, h₃ ⟩;
    grind;
  · rw [ Finset.card_union_of_disjoint ] <;> norm_num;
    · omega;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hx₂ ] ;


/-- **Choi–Erdős–Szemerédi coarse bound (1975)** [CES75]: for every `k ≥ 3` there is
`ε_k > 0` such that (for large enough `N`) every bad `A ⊆ {1,…,N}` has
`|A| ≤ (2/3 − ε_k) N + O(1)`. Specialising to `k = 3` gives, in our setup, some
`θ < 2/3` and `K₀ ∈ ℝ` for which `CoarseBound θ K₀` holds. -/
axiom coarse_bound_ces75 : ∃ θ K0 : ℝ, θ < 2 / 3 ∧ CoarseBound θ K0

/-- **Erdős Problem 865 (Erdős–Sós pairwise-sums, k = 3).** Proved by Cipollini and
GPT Pro [Ci26]: there is a constant `C` such that every `A ⊆ {1,…,N}` with
`|A| ≥ (5/8) N + C` contains distinct `a, b, c ∈ A` whose three pairwise sums
`a+b, a+c, b+c` all lie in `A`. Moreover, the constant `5/8` is best possible:
for every `k ≥ 1`, `N = 8k`, the set `[k, 2k] ∪ [4k, 8k] ⊂ {1,…,N}` is bad and has
`5k + 2 = (5/8) N + 2` elements. -/
theorem erdos_865 :
    (∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), MemRange N A →
        (5 / 8 * N + C ≤ (A.card : ℝ)) → HasTriple A) ∧
    (∀ k : ℕ, 1 ≤ k →
        ∃ A : Finset ℕ, MemRange (8 * k) A ∧ IsBad A ∧ A.card = 5 * k + 2) := by
  refine ⟨?_, sharp⟩
  obtain ⟨θ, K0, hθ, hc⟩ := coarse_bound_ces75
  exact conditional_threshold hθ hc

#print axioms erdos_865
-- 'Erdos865.erdos_865' depends on axioms: [propext, Classical.choice, Erdos865.coarse_bound_ces75, Quot.sound]

end Erdos865
