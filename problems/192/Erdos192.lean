import Mathlib

/-!
# Standalone proof of Erdős Problem 192

Standalone file generated from the KE92 paper workspace. It intentionally
duplicates the shared Keränen proof chain so this file can be posted or copied
without importing the KE92 folder.
-/

/-!
## Source: `PaperCoreDefs.lean`
-/


/-!
# KE92 shared definitions and basic lemmas

Definitions and foundational lemmas for the Keränen 1992 formalization.
Separated from `KE92.lean` so that bounded verification files can
-/

set_option maxHeartbeats 800000

namespace Erdos192

/-! ### Finite-word abelian-square-free definitions -/

def infBlock {α : Type*} (f : ℕ → α) (start len : ℕ) : List α :=
  (List.range len).map (fun j => f (start + j))

def InfAbelianSquareFree {α : Type*} [DecidableEq α] (f : ℕ → α) : Prop :=
  ∀ i l, l > 0 → ¬ (infBlock f i l).Perm (infBlock f (i + l) l)

def FinAbelianSquareFree {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ i l : ℕ, l > 0 → i + 2 * l ≤ w.length →
    ¬ (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l)

/-! ### Parikh walk and 3-term APs -/

def parikhCount {k : ℕ} (f : ℕ → Fin k) (n : ℕ) (c : Fin k) : ℕ :=
  ((Finset.range n).filter (fun j => f j = c)).card

def hasParikhAP {k : ℕ} (f : ℕ → Fin k) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧
    ∀ d : Fin k, parikhCount f a d + parikhCount f c d = 2 * parikhCount f b d

def parikhAPFree {k : ℕ} (f : ℕ → Fin k) : Prop :=
  ¬ hasParikhAP f

/-! ### Key equivalence: abelian-square-free ↔ Parikh-AP-free -/

theorem parikhCount_block {k : ℕ} (f : ℕ → Fin k) (s l : ℕ) (c : Fin k) :
    ((infBlock f s l).filter (· = c)).length =
      parikhCount f (s + l) c - parikhCount f s c := by
  unfold parikhCount;
  rw [ show { j ∈ Finset.range ( s + l ) | f j = c } = Finset.filter ( fun j => f j = c ) ( Finset.range s ) ∪ Finset.filter ( fun j => f j = c ) ( Finset.Ico s ( s + l ) ) from ?_, Finset.card_union_of_disjoint ];
  · rw [ show { j ∈ Finset.Ico s ( s + l ) | f j = c } = Finset.image ( fun j => s + j ) ( Finset.filter ( fun j => f ( s + j ) = c ) ( Finset.range l ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
    · simp +decide [ infBlock ];
      rw [ List.filter_map ] ; aesop;
    · ext; simp [Finset.mem_Ico, Finset.mem_image];
      exact ⟨ fun h => ⟨ ‹_› - s, ⟨ by omega, by simpa [ add_tsub_cancel_of_le h.1.1 ] using h.2 ⟩, by omega ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, ha₂ ⟩ ⟩;
  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ico.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
  · grind

theorem infAbelianSquareFree_iff_parikhAPFree {k : ℕ} (f : ℕ → Fin k) :
    InfAbelianSquareFree f ↔ parikhAPFree f := by
  constructor <;> intro h;
  · rintro ⟨ a, b, c, hab, hbc, h ⟩;
    have h_count_eq : ∀ d : Fin k, ((infBlock f a (b - a)).filter (· = d)).length = ((infBlock f b (c - b)).filter (· = d)).length := by
      intro d;
      rw [ parikhCount_block, parikhCount_block ];
      grind;
    have h_perm : (infBlock f a (b - a)).Perm (infBlock f b (c - b)) := by
      rw [ List.perm_iff_count ];
      simp_all +decide [ List.filter_eq ];
    have h_length_eq : b - a = c - b := by
      have := h_perm.length_eq; simp_all +decide [ infBlock ] ;
    rw [ eq_tsub_iff_add_eq_of_le ] at h_length_eq <;> try linarith;
    subst h_length_eq;
    exact ‹InfAbelianSquareFree f› a ( b - a ) ( Nat.sub_pos_of_lt hab ) ( by simpa [ add_assoc, Nat.add_sub_of_le hab.le ] using h_perm );
  · intro i l hl;
    contrapose! h;
    have h_counts : ∀ c : Fin k, parikhCount f (i + l) c - parikhCount f i c = parikhCount f (i + 2 * l) c - parikhCount f (i + l) c := by
      intro c
      have h_count_eq : ((infBlock f i l).filter (· = c)).length = ((infBlock f (i + l) l).filter (· = c)).length := by
        exact h.filter _ |> List.Perm.length_eq;
      rw [ parikhCount_block, parikhCount_block ] at * ; ring_nf at * ; aesop;
    refine' fun h => h ⟨ i, i + l, i + 2 * l, _, _, _ ⟩ <;> simp_all +decide [ two_mul ];
    intro c; specialize h_counts c; rw [ tsub_eq_iff_eq_add_of_le ] at h_counts;
    · linarith [ Nat.sub_add_cancel ( show parikhCount f ( i + ( l + l ) ) c ≥ parikhCount f ( i + l ) c from by exact Finset.card_mono <| by intros x hx; exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr <| by linarith [ Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1 ], by aesop ⟩ ) ];
    · exact Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.le_add_right _ _

/-! ### The main theorem (Keränen 1992) — basic infrastructure -/

theorem finASF_prefix {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (m : ℕ) (hm : m ≤ w.length) : FinAbelianSquareFree (w.take m) := by
  intro i l hl;
  rw [ List.drop_take, List.drop_take ];
  intro h;
  convert hw i l hl _ using 1;
  · grind;
  · exact h.trans ( by simp )

theorem finASF_drop {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (k : ℕ) : FinAbelianSquareFree (w.drop k) := by
  intro i l hl hlen hperm
  have hlen' : (k + i) + 2 * l ≤ w.length := by
    simp [List.length_drop] at hlen; omega
  apply hw (k + i) l hl hlen'
  rw [List.drop_drop, List.drop_drop] at hperm
  simp only [Nat.add_assoc] at hperm ⊢
  exact hperm

theorem finASF_subword {n : ℕ} (w : List (Fin n)) (hw : FinAbelianSquareFree w)
    (k m : ℕ) (hm : k + m ≤ w.length) : FinAbelianSquareFree (w.drop k |>.take m) :=
  finASF_prefix _ (finASF_drop w hw k) m (by simp [List.length_drop]; omega)

/-! ## Keränen's 85-uniform morphism -/

def hasAbelianSquareAtFin {n : ℕ} (word : List (Fin n)) (i l : Nat) : Bool :=
  if l == 0 then false
  else if i + 2 * l > word.length then false
  else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l)

def isFinASF {n : ℕ} (word : List (Fin n)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      hasAbelianSquareAtFin word i (l + 1))

def keranenG₀ : List (Fin 4) :=
  [0,1,2,0,2,3,2,1,2,3,
   2,0,3,2,3,1,3,0,1,0,
   2,0,1,0,3,1,0,1,2,1,
   3,1,2,1,0,2,1,2,3,2,
   0,2,1,0,1,3,0,1,0,2,
   0,3,2,1,2,3,2,0,2,3,
   1,2,1,0,2,1,2,3,2,0,
   2,3,2,1,3,2,3,0,3,1,
   3,2,1,2,0]

private def shiftFin4 (w : List (Fin 4)) : List (Fin 4) :=
  w.map fun x => ⟨(x.val + 1) % 4, by omega⟩

def keranenG (c : Fin 4) : List (Fin 4) :=
  match c with
  | ⟨0, _⟩ => keranenG₀
  | ⟨1, _⟩ => shiftFin4 keranenG₀
  | ⟨2, _⟩ => shiftFin4 (shiftFin4 keranenG₀)
  | ⟨3, _⟩ => shiftFin4 (shiftFin4 (shiftFin4 keranenG₀))

def applyKeranenG (w : List (Fin 4)) : List (Fin 4) :=
  w.flatMap keranenG

def keranenIterate : ℕ → List (Fin 4)
  | 0 => [(0 : Fin 4)]
  | n + 1 => applyKeranenG (keranenIterate n)

theorem keranenG_length (c : Fin 4) : (keranenG c).length = 85 := by
  fin_cases c <;> native_decide

theorem applyKeranenG_length (w : List (Fin 4)) :
    (applyKeranenG w).length = 85 * w.length := by
  induction w with
  | nil => simp [applyKeranenG]
  | cons a t ih =>
    simp only [applyKeranenG, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih, keranenG_length]; simp [List.length]; ring

theorem keranenIterate_length (n : ℕ) : (keranenIterate n).length = 85 ^ n := by
  induction n with
  | zero => simp [keranenIterate]
  | succ n ih => simp only [keranenIterate, applyKeranenG_length, ih, pow_succ]; ring

theorem isFinASF_sound (w : List (Fin 4)) (h : isFinASF w = true) :
    FinAbelianSquareFree w := by
  intro i l hl hlen hperm
  have key : hasAbelianSquareAtFin w i l = true := by
    unfold hasAbelianSquareAtFin
    have h1 : (l == 0) = false := by simp; omega
    have h2 : (i + 2 * l > w.length) = false := by simp; omega
    simp [h1, h2, List.isPerm_iff, hperm]
  have hfalse : isFinASF w = false := by
    unfold isFinASF
    simp only [Bool.eq_false_iff, Bool.not_not_eq]
    rw [List.any_eq_true]
    exact ⟨i, List.mem_range.mpr (by omega), by
      rw [List.any_eq_true]
      exact ⟨l - 1, List.mem_range.mpr (by omega), by
        show hasAbelianSquareAtFin w i (l - 1 + 1) = true
        rw [Nat.sub_add_cancel hl]; exact key⟩⟩
  simp_all

theorem singleton_finASF (c : Fin 4) : FinAbelianSquareFree [c] := by
  intro i l hl hlen; simp at hlen; omega

theorem isFinASF_complete (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    isFinASF w = true := by
  contrapose! hw;
  unfold isFinASF at hw;
  simp_all +decide [ List.any_eq_true ];
  obtain ⟨ i, hi, j, hj, h ⟩ := hw;
  unfold hasAbelianSquareAtFin at h;
  simp_all +decide [ List.isPerm_iff ];
  exact fun H => H i ( j + 1 ) ( Nat.succ_pos _ ) h.1 h.2

end Erdos192

/-!
## Source: `KeranenBounded.lean`
-/


/-!
# Bounded computational verification of Keränen's morphism preservation (K = 4)

Proves by `native_decide` that Keränen's 85-uniform morphism preserves
abelian-square-freeness for all abelian-square-free words of length ≤ 4.

This covers all potential abelian squares of half-length ≤ 127 in morphism images.

## Role in the proof chain

Combined with `finASF_subword` (localization) and the block-bound finite reduction,
this is part of the chain proving `keranenG_preserves_ASF`.

The K = 5 verification (covering half-length ≤ 170) is split into separate files
`KeranenBounded5a.lean` through `KeranenBounded5d.lean`, each handling one starting
letter. Together they verify all 1024 length-5 words.
-/

set_option maxHeartbeats 4000000

namespace Erdos192

/-- Morphism preservation verified for all words of length 4 by `native_decide`.
For every word `[a,b,c,d]` over `{0,1,2,3}` that is abelian-square-free,
its morphism image `g([a,b,c,d])` (of length 340) is also abelian-square-free. -/
theorem morphism_check_4 :
    ∀ a b c d : Fin 4, isFinASF [a, b, c, d] = true →
    isFinASF (applyKeranenG [a, b, c, d]) = true := by
  native_decide

end Erdos192

/-!
## Source: `KeranenBounded5a.lean`
-/


/-! # Morphism preservation for length-5 words starting with letter 0 -/

set_option maxHeartbeats 4000000

namespace Erdos192

/-- Morphism preservation for length-5 words starting with letter 0.
Verified by `native_decide` over all 4⁴ = 256 inputs. -/
theorem morphism_check_5a :
    ∀ b c d e : Fin 4,
    isFinASF [(0 : Fin 4), b, c, d, e] = true →
    isFinASF (applyKeranenG [(0 : Fin 4), b, c, d, e]) = true := by
  native_decide

end Erdos192

/-!
## Source: `KeranenBounded5b.lean`
-/


/-! # Morphism preservation for length-5 words starting with letter 1 -/

set_option maxHeartbeats 4000000

namespace Erdos192

/-- Morphism preservation for length-5 words starting with letter 1.
Verified by `native_decide` over all 4⁴ = 256 inputs. -/
theorem morphism_check_5b :
    ∀ b c d e : Fin 4,
    isFinASF [(1 : Fin 4), b, c, d, e] = true →
    isFinASF (applyKeranenG [(1 : Fin 4), b, c, d, e]) = true := by
  native_decide

end Erdos192

/-!
## Source: `KeranenBounded5c.lean`
-/


/-! # Morphism preservation for length-5 words starting with letter 2 -/

set_option maxHeartbeats 4000000

namespace Erdos192

/-- Morphism preservation for length-5 words starting with letter 2.
Verified by `native_decide` over all 4⁴ = 256 inputs. -/
theorem morphism_check_5c :
    ∀ b c d e : Fin 4,
    isFinASF [(2 : Fin 4), b, c, d, e] = true →
    isFinASF (applyKeranenG [(2 : Fin 4), b, c, d, e]) = true := by
  native_decide

end Erdos192

/-!
## Source: `KeranenBounded5d.lean`
-/


/-! # Morphism preservation for length-5 words starting with letter 3 -/

set_option maxHeartbeats 4000000

namespace Erdos192

/-- Morphism preservation for length-5 words starting with letter 3.
Verified by `native_decide` over all 4⁴ = 256 inputs. -/
theorem morphism_check_5d :
    ∀ b c d e : Fin 4,
    isFinASF [(3 : Fin 4), b, c, d, e] = true →
    isFinASF (applyKeranenG [(3 : Fin 4), b, c, d, e]) = true := by
  native_decide

end Erdos192

/-!
## Source: `BlockBound.lean`
-/


/-!
# Block bound: computational helpers (base file)

Core definitions and the spanning-6/delta-zero checks.
Spanning-7, spanning-8, Parikh norm bound, and 3-letter bound
are in separate files to manage native_decide compilation time.
-/

set_option maxHeartbeats 8000000

namespace Erdos192

/-! ### Spanning-6 abelian square check -/

def hasSpanning6AS (w : List (Fin 4)) : Bool :=
  let gw := applyKeranenG w
  (List.range 85).any fun i =>
    let lMin := (426 - i + 1) / 2
    let lMax := (510 - i) / 2
    (List.range (lMax - lMin + 1)).any fun k =>
      let ll := lMin + k
      (gw.drop i |>.take ll).isPerm (gw.drop (i + ll) |>.take ll)

/-- No ASF word of length 6 has a spanning-6 abelian square in its morphism image. -/
theorem no_spanning6_abelianSquare :
    ∀ a b c d e f : Fin 4,
      isFinASF [a, b, c, d, e, f] = true →
      hasSpanning6AS [a, b, c, d, e, f] = false := by native_decide

/-! ### δ = 0 impossibility -/

def cumParikhCount (a : Fin 4) (k : Nat) (c : Fin 4) : Nat :=
  ((keranenG a).take k).count c

def sliceParikhCount (a : Fin 4) (lo hi : Nat) (c : Fin 4) : Int :=
  (cumParikhCount a hi c : Int) - (cumParikhCount a lo c : Int)

def boundaryDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let t := (2 * s + 85 * 1000 - r) % 85
  sliceParikhCount wb s 85 c + sliceParikhCount we 0 t c
  - sliceParikhCount wa r 85 c - sliceParikhCount wb 0 s c

/-! ### Parikh norm bound definitions -/

/-- Product of adjugate of M^T with delta vector. -/
def adjMTtimesDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d : Fin 4 → Int := boundaryDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

end Erdos192

/-!
## Source: `BlockBoundParikh.lean`
-/


/-! # Parikh norm bound and 3-letter ASF bound -/

set_option maxHeartbeats 8000000

namespace Erdos192

/-- Decidable ASF check for `Fin 3` words. -/
def isFinASF3 (word : List (Fin 3)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      let l := l + 1
      if i + 2 * l > word.length then false
      else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l))

/-- **3-letter ASF bound.** No ASF word on 3 letters has length ≥ 8. -/
theorem max_asf_3letters :
    ∀ a b c d e f g h : Fin 3,
      isFinASF3 [a, b, c, d, e, f, g, h] = false := by native_decide

end Erdos192

/-!
## Source: `BlockBoundParikhBridge.lean`
-/


/-!
# Parikh bridge infrastructure for the spanning abelian square elimination

This file contains the Parikh-matrix bridge infrastructure for proving that
ASF words of length m ≥ 14 have no spanning abelian square in their
Keränen morphism image.

## Overview

A *spanning* abelian square in g(w) at offset r with half-length L means:
- The AS covers all m = w.length blocks: (r + 2L - 1)/85 + 1 = m
- The two halves have the same Parikh vector (letter counts)

The midpoint falls in block k = (r + L) / 85 with offset s = (r + L) % 85.
The boundary letters are wa = w[0], wb = w[k], we = w[m-1].

The Parikh equality of the two halves yields the matrix equation:
  M · v = δ(wa, wb, we, r, s)
where v is the inner block Parikh defect and M is the 4×4 Parikh matrix
of the morphism.

## Computationally verified properties

1. `parikh_norm_bound` (in BlockBoundParikh.lean): ‖v‖₁ ≤ 3
2. `parikh_v_sum_zero_norm_le2`: For Σv = 0 and ‖v‖₁ ≤ 2, v ∈ {e_X − e_Y : X,Y ∈ {wa,wb,we}}
3. `parikh_v_norm1_is_wb`: For |Σv| = 1 and ‖v‖₁ = 1, v = Σv · e_{wb}
4. The ‖v‖₁ = 3 case (even m only, 40 patterns) requires deeper analysis.
-/

set_option maxHeartbeats 8000000

namespace Erdos192

/-! ### Computational verification of v-pattern structure -/

/-- Helper: compute v from boundary configuration -/
def parikhSolutionVec (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  adjMTtimesDelta wa wb we r s c / 43435

/-- Helper: check if solution exists (divisibility) -/
def hasParikhSolution (wa wb we : Fin 4) (r s : Nat) : Bool :=
  adjMTtimesDelta wa wb we r s 0 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 1 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 2 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 3 % 43435 = 0

end Erdos192

/-!
## Source: `BlockBoundParikhFormal.lean`
-/


/-!
# Formal Parikh bridge infrastructure

Proved infrastructure for the spanning abelian square elimination:
- v-pattern classification for ‖v‖₁ = 3 (completing the Parikh v analysis)
- Block take decomposition (key list identity for the Parikh bridge)
- Count slice decomposition (Parikh of g(w) slices)
- Spanning Perm → hasSpanningAS = true (direction needed for contradiction)

## Remaining source lemma

The full Parikh bridge (spanning AS → AS in w → contradiction with ASF)
requires the **block-decomposition count identity**, which connects the Perm
condition on g(w) halves to the inner Parikh defect of w via the matrix
equation M^T v = δ_actual. This identity involves:

1. Expressing count(c, g(w).take(n)) via `applyKeranenG_take_blocks` (DONE).
2. Relating the Perm equality to the inner block-letter counts (requires
   careful treatment of the t = r+2L−85(m−1) boundary offset, especially
   the t = 85 edge case where the code's `boundaryDelta` uses t_code = 0).
3. Applying the v-pattern classification (DONE for all ‖v‖₁ ≤ 3).
4. Algebraically constructing the AS in w from the classified v pattern.

The t = 85 edge case has been computationally verified to NOT produce the
problematic v patterns (confirmed by `checkT85Issue` in interactive mode),
so the full bridge argument is mathematically sound.
-/

set_option maxHeartbeats 8000000

namespace Erdos192

/-! ### Block take decomposition -/

/-- Key block decomposition: taking 85k+s from g(w) splits into
    complete blocks g(w.take k) and a partial block g(w[k]).take(s). -/
theorem applyKeranenG_take_blocks (w : List (Fin 4)) (k s : ℕ)
    (hk : k < w.length) (hs : s ≤ 85) :
    (applyKeranenG w).take (85 * k + s) =
    applyKeranenG (w.take k) ++ (keranenG (w.get ⟨k, hk⟩)).take s := by
  induction' k with k ih generalizing w s
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ applyKeranenG ]
    · contradiction
    · exact Or.inr ( by rw [ keranenG_length ] ; linarith )
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ,]
    · contradiction
    · contradiction
    · simp_all +decide [ applyKeranenG ]
      rw [ ← ih ]
      · simp +arith +decide [ List.take_append, keranenG_length ]
      · grind
      · grind

end Erdos192

/-!
## Source: `BlockBoundSpanning.lean`
-/


/-!
# Spanning abelian square elimination for m ≥ 14
-/

set_option maxHeartbeats 8000000

namespace Erdos192

/-! ### Basic lemmas -/

theorem count_flatMap_sum {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → List β) (b : β) :
    (l.flatMap f).count b = (l.map (fun a => (f a).count b)).sum := by
  induction l <;> aesop

theorem applyKeranenG_append (l1 l2 : List (Fin 4)) :
    applyKeranenG (l1 ++ l2) = applyKeranenG l1 ++ applyKeranenG l2 := by
  simp [applyKeranenG, List.flatMap_append]

/-! ### Count decomposition lemmas -/

/-
Count of g(w.take k) = g(w[0]).count + g(inner_left).count, for k ≥ 1.
-/
theorem count_take_split_head (w : List (Fin 4)) (k : ℕ) (c : Fin 4)
    (hk : 1 ≤ k) (hkw : k ≤ w.length) :
    (applyKeranenG (w.take k)).count c =
    (keranenG (w.get ⟨0, by omega⟩)).count c +
    (applyKeranenG (w.drop 1 |>.take (k - 1))).count c := by
  generalize_proofs at *;
  rcases k with ( _ | k );
  · contradiction;
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide;
    · native_decide +revert;
    · unfold applyKeranenG; aesop;

/-
Count of g(w.take (m-1)) splits as g(w[0]) + g(inner_left) + g(w[k]) + g(inner_right).
-/
theorem count_take_full_split (w : List (Fin 4)) (k m : ℕ) (c : Fin 4)
    (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ m) (hm : m ≤ w.length) :
    (applyKeranenG (w.take (m - 1))).count c =
    (keranenG (w.get ⟨0, by omega⟩)).count c +
    (applyKeranenG (w.drop 1 |>.take (k - 1))).count c +
    (keranenG (w.get ⟨k, by omega⟩)).count c +
    (applyKeranenG (w.drop (k + 1) |>.take (m - 2 - k))).count c := by
  -- Apply the count_take_split_head lemma to split the count into the sum of the counts of the individual parts.
  have h_split : List.count c (applyKeranenG (List.take (m - 1) w)) = List.count c (applyKeranenG (List.take k w)) + List.count c (applyKeranenG (List.take (m - 1 - k) (List.drop k w))) := by
    rw [ show List.take ( m - 1 ) w = List.take k w ++ List.take ( m - 1 - k ) ( List.drop k w ) from ?_, applyKeranenG_append ];
    · rw [ List.count_append ];
    · rw [ ← List.take_add, Nat.add_sub_of_le ( by omega ) ];
  rw [ h_split, count_take_split_head ];
  convert congr_arg _ ( count_take_split_head _ _ _ _ _ ) using 1;
  all_goals norm_num [ Nat.sub_sub ];
  grind;
  · omega;
  · omega;
  · linarith;
  · linarith

/-! ### Parikh matrix identity -/

def parikhM (c a : Fin 4) : ℕ := (keranenG a).count c

def adjRow (row : Fin 4) (v : Fin 4 → Int) : Int :=
  match row with
  | 0 => -701 * v 0 + (-531) * v 1 + 4059 * v 2 + (-2316) * v 3
  | 1 => (-2316) * v 0 + (-701) * v 1 + (-531) * v 2 + 4059 * v 3
  | 2 => 4059 * v 0 + (-2316) * v 1 + (-701) * v 2 + (-531) * v 3
  | 3 => (-531) * v 0 + 4059 * v 1 + (-2316) * v 2 + (-701) * v 3

theorem adj_times_M :
    ∀ c d : Fin 4,
      adjRow c (fun j => (parikhM j d : Int)) =
      43435 * (if c = d then 1 else 0) := by native_decide

/-! ### v-pattern classification -/

def vGivesSomeAS (wa wb we : Fin 4) (v : Fin 4 → Int) : Bool :=
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) - (if c = we then 1 else 0) == 0) ||
  ((List.finRange 4).all fun c => v c - (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) - (if c = we then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) + (if c = wb then 1 else 0) + v c - (if c = we then 1 else 0) == 0)

theorem v_pattern_gives_AS_normal :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      vGivesSomeAS wa wb we (parikhSolutionVec wa wb we r.val s.val) = true := by
  native_decide

theorem v_pattern_gives_AS_t85 :
    ∀ wa wb we : Fin 4, ∀ r s : Fin 85,
      hasParikhSolution wa wb we r.val s.val = true →
      (2 * s.val + 85 * 1000 - r.val) % 85 = 0 →
      vGivesSomeAS wa wb we
        (fun c => parikhSolutionVec wa wb we r.val s.val c +
          if c = we then 1 else 0) = true := by
  native_decide

/-! ### Map sum regrouping -/

/-
For Fin 4 lists: (l.map f).sum = Σ_a f(a) * l.count a
-/
theorem map_sum_eq_weighted_count (l : List (Fin 4)) (f : Fin 4 → ℕ) :
    (l.map f).sum = f 0 * l.count 0 + f 1 * l.count 1 + f 2 * l.count 2 + f 3 * l.count 3 := by
  induction' l with x xs ih;
  · rfl;
  · fin_cases x <;> simp +decide [ List.count ] <;> linarith!

/-! ### Main bridge -/

/-
Core inner count identity: the Parikh bridge equation.
-/
theorem inner_count_bridge (w : List (Fin 4)) (r L : ℕ) (c : Fin 4)
    (hm_ge : w.length ≥ 7) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ 85 * w.length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    let k := (r + L) / 85
    let s := (r + L) % 85
    let m := w.length
    let t := r + 2 * L - 85 * (m - 1)
    ((applyKeranenG (w.drop 1 |>.take (k - 1))).count c : Int) -
    ((applyKeranenG (w.drop (k + 1) |>.take (m - 2 - k))).count c : Int) =
    boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨k, by omega⟩) (w.get ⟨m - 1, by omega⟩) r s c +
    (if t = 85 then ((keranenG (w.get ⟨m - 1, by omega⟩)).count c : Int) else 0) := by
  refine' Eq.symm ( _ );
  have h_eq : 2 * ((applyKeranenG (w.take ((r + L) / 85))).count c + ((keranenG (w.get ⟨(r + L) / 85, by
    omega⟩)).take ((r + L) % 85)).count c) =
    ((keranenG (w.get ⟨0, by
      linarith⟩)).take r).count c +
    ((applyKeranenG (w.take (w.length - 1))).count c) +
    ((keranenG (w.get ⟨w.length - 1, by
      exact Nat.pred_lt ( ne_bot_of_gt hm_ge )⟩)).take (r + 2 * L - 85 * (w.length - 1))).count c := by
      all_goals generalize_proofs at *;
      have h_eq : 2 * ((applyKeranenG w).take (r + L)).count c = ((applyKeranenG w).take r).count c + ((applyKeranenG w).take (r + 2 * L)).count c := by
        have h_eq : ((applyKeranenG w).take (r + L)).count c - ((applyKeranenG w).take r).count c = ((applyKeranenG w).take (r + 2 * L)).count c - ((applyKeranenG w).take (r + L)).count c := by
          have h_eq : ((applyKeranenG w).drop r |>.take L).count c = ((applyKeranenG w).drop (r + L) |>.take L).count c := by
            exact hperm.count_eq _;
          convert h_eq using 1;
          · grind;
          · rw [ show r + 2 * L = ( r + L ) + L by ring, List.take_add ];
            rw [ List.count_append, add_tsub_cancel_left ];
        grind;
      have h_eq : ((applyKeranenG w).take (r + L)).count c = ((applyKeranenG (w.take ((r + L) / 85))).count c) + ((keranenG (w.get ⟨(r + L) / 85, by
        assumption⟩)).take ((r + L) % 85)).count c := by
        all_goals generalize_proofs at *;
        rw [ ← List.count_append, ← applyKeranenG_take_blocks ];
        · rw [ Nat.div_add_mod ];
        · exact Nat.le_of_lt ( Nat.mod_lt _ ( by decide ) )
      generalize_proofs at *;
      have h_eq : ((applyKeranenG w).take (r + 2 * L)).count c = ((applyKeranenG (w.take (w.length - 1))).count c) + ((keranenG (w.get ⟨w.length - 1, by
        grind +splitImp⟩)).take (r + 2 * L - 85 * (w.length - 1))).count c := by
        all_goals generalize_proofs at *;
        have h_eq : (applyKeranenG w).take (r + 2 * L) = applyKeranenG (w.take (w.length - 1)) ++ (keranenG (w.get ⟨w.length - 1, by
          grind +splitImp⟩)).take (r + 2 * L - 85 * (w.length - 1)) := by
          all_goals generalize_proofs at *;
          convert applyKeranenG_take_blocks w ( w.length - 1 ) ( r + 2 * L - 85 * ( w.length - 1 ) ) _ _ using 1 <;> norm_num [ hspan.symm ];
          · rw [ Nat.add_sub_of_le ( by omega ) ];
          · omega
        generalize_proofs at *;
        rw [ h_eq, List.count_append ]
      generalize_proofs at *;
      have h_eq : ((applyKeranenG w).take r).count c = ((keranenG (w.get ⟨0, by
        linarith⟩)).take r).count c := by
        all_goals generalize_proofs at *;
        have h_eq : (applyKeranenG w).take r = (keranenG (w.get ⟨0, by
          linarith⟩)).take r := by
          all_goals generalize_proofs at *;
          convert applyKeranenG_take_blocks w 0 r _ _ using 1 <;> norm_num [ hr.le ]
        generalize_proofs at *;
        rw [h_eq]
      generalize_proofs at *;
      grind
  generalize_proofs at *;
  by_cases hk : 1 ≤ (r + L) / 85;
  · have h_eq : (applyKeranenG (w.take ((r + L) / 85))).count c = ((keranenG (w.get ⟨0, by
      linarith⟩)).count c) + ((applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))).count c) := by
      all_goals generalize_proofs at *;
      convert count_take_split_head w ( ( r + L ) / 85 ) c hk ( by omega ) using 1
    generalize_proofs at *;
    have h_eq : (applyKeranenG (w.take (w.length - 1))).count c = ((keranenG (w.get ⟨0, by
      linarith⟩)).count c) + ((applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))).count c) + ((keranenG (w.get ⟨(r + L) / 85, by
      assumption⟩)).count c) + ((applyKeranenG (w.drop ((r + L) / 85 + 1) |>.take (w.length - 2 - (r + L) / 85))).count c) := by
      all_goals generalize_proofs at *;
      convert count_take_full_split w ( ( r + L ) / 85 ) w.length c hk ( by omega ) ( by omega ) using 1
    generalize_proofs at *;
    unfold boundaryDelta;
    unfold sliceParikhCount;
    unfold cumParikhCount;
    split_ifs <;> simp_all +decide
    · rw [ show ( 2 * ( ( r + L ) % 85 ) + 85000 - r ) % 85 = 0 from ?_ ] ; norm_num ; ring;
      · rw [ show List.take 85 ( keranenG w[0] ) = keranenG w[0] from ?_, show List.take 85 ( keranenG w[w.length - 1] ) = keranenG w[w.length - 1] from ?_ ] at * <;> norm_num at *;
        · rw [ show List.take 85 ( keranenG w[(r + L) / 85] ) = keranenG w[(r + L) / 85] from ?_ ] at *
          · grind;
          · rw [ List.take_of_length_le ] ; norm_num [ keranenG_length ];
        · exact le_of_eq ( keranenG_length _ );
        · exact le_of_eq ( keranenG_length _ );
      · omega;
    · rw [ show List.take 85 ( keranenG w[(r + L) / 85] ) = keranenG w[(r + L) / 85] from ?_, show List.take 85 ( keranenG w[0] ) = keranenG w[0] from ?_ ];
      · rw [ show ( 2 * ( ( r + L ) % 85 ) + 85000 - r ) % 85 = ( r + 2 * L - 85 * ( w.length - 1 ) ) % 85 from ?_ ];
        · rw [ show ( r + 2 * L - 85 * ( w.length - 1 ) ) % 85 = ( r + 2 * L - 85 * ( w.length - 1 ) ) from ?_ ];
          · grind;
          · omega;
        · omega;
      · exact List.take_of_length_le ( by simp +decide [ keranenG_length ] );
      · exact List.take_of_length_le ( by simp +decide [ keranenG_length ] );
  · omega

/-! ### Helper lemmas for the algebraic chain -/

/-- flatMap count = Parikh matrix times letter-count vector -/
theorem applyKeranenG_count_as_sum (l : List (Fin 4)) (c : Fin 4) :
    (applyKeranenG l).count c =
    parikhM c 0 * l.count 0 + parikhM c 1 * l.count 1 +
    parikhM c 2 * l.count 2 + parikhM c 3 * l.count 3 := by
  unfold applyKeranenG parikhM
  rw [count_flatMap_sum, map_sum_eq_weighted_count]

/-- adjRow is linear over 4 terms -/
private theorem adjRow_linear4 (d : Fin 4) (x : Fin 4 → Int) (f : Fin 4 → Fin 4 → Int) :
    adjRow d (fun c => x 0 * f 0 c + x 1 * f 1 c + x 2 * f 2 c + x 3 * f 3 c) =
    x 0 * adjRow d (f 0) + x 1 * adjRow d (f 1) + x 2 * adjRow d (f 2) + x 3 * adjRow d (f 3) := by
  fin_cases d <;> simp [adjRow] <;> ring

/-- If M·x = δ (as Fin 4 sums), then 43435 * x d = adjRow d δ -/
theorem adj_solve (v : Fin 4 → Int) (δ : Fin 4 → Int) (d : Fin 4)
    (h : ∀ c : Fin 4, (parikhM c 0 : Int) * v 0 + (parikhM c 1 : Int) * v 1 +
                       (parikhM c 2 : Int) * v 2 + (parikhM c 3 : Int) * v 3 = δ c) :
    43435 * v d = adjRow d δ := by
  have hd : δ = fun c => (parikhM c 0 : Int) * v 0 + (parikhM c 1 : Int) * v 1 +
                 (parikhM c 2 : Int) * v 2 + (parikhM c 3 : Int) * v 3 := by
    ext c; exact (h c).symm
  subst hd
  rw [show (fun c => (↑(parikhM c 0)) * v 0 + (↑(parikhM c 1)) * v 1 +
                 (↑(parikhM c 2)) * v 2 + (↑(parikhM c 3)) * v 3) =
    (fun c => v 0 * (↑(parikhM c 0)) + v 1 * (↑(parikhM c 1)) +
              v 2 * (↑(parikhM c 2)) + v 3 * (↑(parikhM c 3))) from by ext; ring]
  rw [adjRow_linear4 d v (fun a c => (parikhM c a : Int))]
  simp only [adj_times_M]
  fin_cases d <;> simp <;> ring

/-- adjMTtimesDelta equals adjRow applied to boundaryDelta -/
theorem adjMTtimesDelta_eq_adjRow (wa wb we : Fin 4) (r s : ℕ) (d : Fin 4) :
    adjMTtimesDelta wa wb we r s d = adjRow d (boundaryDelta wa wb we r s) := by
  fin_cases d <;> simp [adjMTtimesDelta, adjRow]

/-- adjRow is additive -/
theorem adjRow_add (d : Fin 4) (f g : Fin 4 → Int) :
    adjRow d (fun c => f c + g c) = adjRow d f + adjRow d g := by
  fin_cases d <;> simp [adjRow] <;> ring

/-- adjRow of scaled indicator -/
theorem adjRow_ite_parikhM (d we : Fin 4) :
    adjRow d (fun c => (parikhM c we : Int)) = 43435 * if d = we then 1 else 0 := by
  exact adj_times_M d we

end Erdos192

/-!
## Source: `BlockBoundSpanningChain.lean`
-/


/-!
# Algebraic chain: inner defect → vGivesSomeAS → False
-/

set_option maxHeartbeats 8000000

namespace Erdos192

theorem inner_defect_gives_AS (w : List (Fin 4))
    (hm_ge : w.length ≥ 7) (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ 85 * w.length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    let k := (r + L) / 85
    let m := w.length
    let wa := w.get ⟨0, by omega⟩
    let wb := w.get ⟨k, by omega⟩
    let we := w.get ⟨m - 1, by omega⟩
    let inner_left := w.drop 1 |>.take (k - 1)
    let inner_right := w.drop (k + 1) |>.take (m - 2 - k)
    let v : Fin 4 → Int := fun a => (inner_left.count a : Int) - (inner_right.count a : Int)
    vGivesSomeAS wa wb we v = true := by
  have h_inner_count_bridge : ∀ c : Fin 4, ((List.count c (applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))) : Int) - (List.count c (applyKeranenG (w.drop ((r + L) / 85 + 1) |>.take (w.length - 2 - ((r + L) / 85)))) : Int)) = boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85) c + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then (List.count c (keranenG (w.get ⟨w.length - 1, by omega⟩)) : Int) else 0) := by
    intros c
    apply inner_count_bridge w r L c hm_ge hL hr hlen hspan hperm;
  have h_parikhSolutionVec_applyKeranenG : ∀ a : Fin 4, ∀ l : List (Fin 4), (List.count a (applyKeranenG l) : Int) = ∑ c : Fin 4, (parikhM a c : Int) * (List.count c l) := by
    intros a l
    have h_applyKeranenG_count_as_sum : (List.count a (applyKeranenG l) : Int) = ∑ c : Fin 4, (parikhM a c : Int) * (List.count c l) := by
      have := applyKeranenG_count_as_sum l a
      simp +decide [ this, Fin.sum_univ_four ];
    convert h_applyKeranenG_count_as_sum using 1;
  have h_adj_solve : ∀ a : Fin 4, 43435 * (List.count a (List.take ((r + L) / 85 - 1) (List.drop 1 w)) - List.count a (List.take (w.length - 2 - ((r + L) / 85)) (List.drop ((r + L) / 85 + 1) w)) : ℤ) = adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then adjRow a (fun c => (parikhM c (w.get ⟨w.length - 1, by omega⟩) : ℤ)) else 0) := by
    intro a
    have h_adj_solve_step : ∑ c : Fin 4, (parikhM a c : ℤ) * (List.count c (List.take ((r + L) / 85 - 1) (List.drop 1 w)) - List.count c (List.take (w.length - 2 - ((r + L) / 85)) (List.drop ((r + L) / 85 + 1) w)) : ℤ) = boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85) a + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then (List.count a (keranenG (w.get ⟨w.length - 1, by omega⟩)) : ℤ) else 0) := by
      convert h_inner_count_bridge a using 1;
      simp +decide [ h_parikhSolutionVec_applyKeranenG, mul_sub ];
    convert adj_solve ( fun c => ( List.count c ( List.take ( ( r + L ) / 85 - 1 ) ( List.drop 1 w ) ) - List.count c ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) : ℤ ) ) ( fun c => boundaryDelta ( w.get ⟨ 0, by omega ⟩ ) ( w.get ⟨ ( r + L ) / 85, by omega ⟩ ) ( w.get ⟨ w.length - 1, by omega ⟩ ) r ( ( r + L ) % 85 ) c + if r + 2 * L - 85 * ( w.length - 1 ) = 85 then ( List.count c ( keranenG ( w.get ⟨ w.length - 1, by omega ⟩ ) ) : ℤ ) else 0 ) a _ using 1;
    · split_ifs <;> simp +decide [ *, adjRow_add ];
      rfl;
    · intro c; specialize h_inner_count_bridge c; simp_all +decide [ Fin.sum_univ_four ] ;
      grind;
  have h_adj_solve : ∀ a : Fin 4, adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) % 43435 = 0 := by
    intro a
    specialize h_adj_solve a
    have h_div : 43435 ∣ adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) := by
      split_ifs at h_adj_solve <;> norm_num [ adjRow_ite_parikhM ] at h_adj_solve ⊢ <;> omega
    exact Int.emod_eq_zero_of_dvd h_div;
  by_cases h : r + 2 * L - 85 * ( w.length - 1 ) = 85 <;> simp_all +decide [ adjRow_ite_parikhM ];
  · have := v_pattern_gives_AS_t85 w[0] w[(r + L) / 85] w[w.length - 1] ⟨r, hr⟩ ⟨(r + L) % 85, Nat.mod_lt _ (by decide)⟩; simp_all +decide [ hasParikhSolution ] ;
    convert this _ _ _ _ _ using 2;
    any_goals omega;
    · ext c; specialize ‹∀ a : Fin 4, 43435 * ( ↑ ( List.count a ( List.take ( ( r + L ) / 85 - 1 ) w.tail ) ) - ↑ ( List.count a ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) ) ) = adjRow a ( boundaryDelta w[0] w[( r + L ) / 85] w[w.length - 1] r ( ( r + L ) % 85 ) ) + if a = w[w.length - 1] then 43435 else 0› c; simp_all +decide [ parikhSolutionVec ] ;
      rw [ adjMTtimesDelta_eq_adjRow ];
      split_ifs at * <;> omega;
    · convert h_adj_solve 0 using 1;
    · convert h_adj_solve 1 using 1;
    · convert h_adj_solve 2 using 1;
    · convert h_adj_solve 3 using 1;
  · convert v_pattern_gives_AS_normal w[0] w[(r + L) / 85] w[w.length - 1] ⟨r, hr⟩ ⟨(r + L) % 85, Nat.mod_lt _ (by decide)⟩ _ using 1;
    · unfold parikhSolutionVec; simp +decide [ *, adjMTtimesDelta_eq_adjRow ] ;
      congr! 2;
      exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by decide ) ( by linarith [ ‹∀ a : Fin 4, 43435 * ( ↑ ( List.count a ( List.take ( ( r + L ) / 85 - 1 ) w.tail ) ) - ↑ ( List.count a ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) ) ) = adjRow a ( boundaryDelta w[0] w[( r + L ) / 85] w[w.length - 1] r ( ( r + L ) % 85 ) ) › ‹_› ] ) );
    · unfold hasParikhSolution; simp +decide
      exact ⟨ ⟨ ⟨ h_adj_solve 0, h_adj_solve 1 ⟩, h_adj_solve 2 ⟩, h_adj_solve 3 ⟩

/-! ### List counting helpers -/

theorem sum_count_eq_length (l : List (Fin 4)) :
    (l.count 0 : Int) + l.count 1 + l.count 2 + l.count 3 = l.length := by
  induction l <;> simp +decide [ * ] ; ring;
  rename_i k hk ih; fin_cases k <;> simp +decide at ih ⊢ <;> linarith;

private theorem indicator_sum_fin4 (a : Fin 4) :
    (if (0:Fin 4) = a then (1:Int) else 0) + (if 1 = a then 1 else 0) +
    (if 2 = a then 1 else 0) + (if 3 = a then 1 else 0) = 1 := by
  fin_cases a <;> simp

/-! ### Pattern-specific contradiction lemmas -/

private theorem case1_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 1)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) -
      (if c = w.get ⟨k, hkm⟩ then 1 else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 1)).count c : Int) = 0) : False := by
  -- Apply `hw` with `i = 0` and `l = k` to derive a contradiction.
  specialize hw 0 k hk1 (by linarith);
  contrapose! hw;
  rw [ List.perm_iff_count ];
  intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide
  rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ List.take_succ_cons ];
  · cases hm;
  · rw [ List.drop_eq_getElem_cons ];
    grind +qlia;
    grind

private theorem case2_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 1)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 1)).count c : Int) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) = 0) : False := by
  convert hw 1 k ?_ ?_ using 1;
  · simp +zetaDelta at *;
    rw [ List.perm_iff_count ];
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ List.take_add_one ] ;
    simp_all +decide [ two_mul, add_assoc, List.count ];
    grind;
  · linarith;
  · grind

private theorem case3_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 2 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 2)).count c : Int) -
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) = 0) : False := by
  have hbad := hw 1 (k - 1) (by omega) (by omega)
  apply hbad
  rw [List.perm_iff_count]
  intro c
  specialize h c
  have hsecond :
      (w.drop (1 + (k - 1)) |>.take (k - 1)) =
        w.get ⟨k, hkm⟩ :: (w.drop (k + 1) |>.take (k - 2)) := by
    rw [show 1 + (k - 1) = k by omega, List.drop_eq_getElem_cons hkm,
      show k - 1 = Nat.succ (k - 2) by omega]
    rfl
  grind

private theorem case4_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 2)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take k).count c : Int) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) = 0) : False := by
  convert hw 1 k ?_ ?_ using 1;
  · simp +decide [ List.perm_iff_count, add_comm 1 k ];
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ List.take_add_one ] ;
    grind +qlia;
  · linarith;
  · lia

private theorem case5_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) -
      (if c = w.get ⟨k, hkm⟩ then 1 else 0) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 2)).count c : Int) = 0) : False := by
  have := hw 0 k ( by linarith ) ( by linarith ) ; simp_all +decide ;
  contrapose! this; simp_all +decide [ List.perm_iff_count ] ;
  intro c; specialize h c; rcases k with ( _ | _ | k ) <;> simp_all +decide [ List.take ] ;
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | w ⟩ ⟩ ) <;> simp_all +decide [ List.count ];
    · lia;
    · lia;
    · lia;
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ ];
    · cases hm;
    · rw [ List.drop_eq_getElem_cons ];
      rw [ List.take_cons ] ; norm_num [ List.count_cons ] ; ring;
      all_goals norm_num [ add_comm 1, List.take_add_one ] at *;
      grind +splitImp;
      grind +splitImp

private theorem case6_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 2)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take k).count c : Int) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) = 0) : False := by
  have := hw 0 ( k + 1 ) ?_ ?_ <;> simp_all +decide [ List.take_add ];
  · refine' this ( List.perm_iff_count.mpr _ );
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, List.count ] ;
    · contradiction;
    · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ List.take ];
      · grind;
      · simp_all +decide [ List.countP_cons, List.take_add_one ];
        grind;
  · linarith

/-! ### Main bridge -/

private theorem vGivesSomeAS_cases (wa wb we : Fin 4) (v : Fin 4 → Int)
    (h : vGivesSomeAS wa wb we v = true) :
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) + v c = 0) ∨
    (∀ c : Fin 4, v c + (if c = wb then (1:Int) else 0) - (if c = we then 1 else 0) = 0) ∨
    (∀ c : Fin 4, v c - (if c = wb then (1:Int) else 0) = 0) ∨
    (∀ c : Fin 4, v c + (if c = wb then (1:Int) else 0) = 0) ∨
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) - (if c = we then 1 else 0) + v c = 0) ∨
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) + (if c = wb then 1 else 0) + v c - (if c = we then 1 else 0) = 0) := by
  unfold vGivesSomeAS at h
  repeat rw [Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;>
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  · left; exact fun c => by linarith [h c]
  · right; left; exact fun c => by linarith [h c]
  · right; right; left; exact fun c => by linarith [h c]
  · right; right; right; left; exact fun c => by linarith [h c]
  · right; right; right; right; left; exact fun c => by linarith [h c]
  · right; right; right; right; right; exact fun c => by linarith [h c]

theorem no_spanning_large (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hm : w.length ≥ 7)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  rw [applyKeranenG_length] at hlen
  set k := (r + L) / 85
  have hk1 : k ≥ 1 := by omega
  have hkm : k < w.length := by omega
  -- Get vGivesSomeAS
  have hvas := inner_defect_gives_AS w hm r L hL hr hlen hspan hperm
  -- Extract Prop-level conditions
  obtain hc1 | hc2 | hc3 | hc4 | hc5 | hc6 := vGivesSomeAS_cases _ _ _ _ hvas
  -- For each case: derive length constraint, apply case lemma
  -- Helper for sum(v)
  all_goals (
    set il := w.drop 1 |>.take (k - 1)
    set ir := w.drop (k + 1) |>.take (w.length - 2 - k)
    have hil : il.length = k - 1 := by simp [il, List.length_take]; omega
    have hir : ir.length = w.length - 2 - k := by simp [ir, List.length_take, List.length_drop]; omega
    have hil_cast : (↑(il.length) : Int) = (k : Int) - 1 := by omega
    have hir_cast : (↑(ir.length) : Int) = (w.length : Int) - 2 - k := by omega
    )
  · -- Pattern 1: sum(v) = 0, m = 2k+1
    have hmeq : w.length = 2 * k + 1 := by
      have := hc1 0; have := hc1 1; have := hc1 2; have := hc1 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 1 := by omega
    exact case1_false w hw k hk1 hkm hmeq (fun c => by
      have := hc1 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 2: sum(v) = 0, m = 2k+1
    have hmeq : w.length = 2 * k + 1 := by
      have := hc2 0; have := hc2 1; have := hc2 2; have := hc2 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 1 := by omega
    exact case2_false w hw k hk1 hkm hmeq (fun c => by
      have := hc2 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 3: sum(v) = 1, m = 2k
    have hmeq : w.length = 2 * k := by
      have := hc3 0; have := hc3 1; have := hc3 2; have := hc3 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 2 := by omega
    exact case3_false w hw k (by omega) hkm hmeq (fun c => by
      have := hc3 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 4: sum(v) = -1, m = 2k+2
    have hmeq : w.length = 2 * k + 2 := by
      have := hc4 0; have := hc4 1; have := hc4 2; have := hc4 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k := by omega
    exact case4_false w hw k hk1 hkm hmeq (fun c => by
      have := hc4 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 5: sum(v) = 1, m = 2k
    have hmeq : w.length = 2 * k := by
      have := hc5 0; have := hc5 1; have := hc5 2; have := hc5 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 2 := by omega
    exact case5_false w hw k (by omega) hkm hmeq (fun c => by
      have := hc5 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 6: sum(v) = -1, m = 2k+2
    have hmeq : w.length = 2 * k + 2 := by
      have := hc6 0; have := hc6 1; have := hc6 2; have := hc6 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k := by omega
    exact case6_false w hw k hk1 hkm hmeq (fun c => by
      have := hc6 c; simp only [ir, hirk] at this; linarith)

end Erdos192

/-!
## Source: `BlockBoundBridge.lean`
-/


/-!
# Block bound bridge lemmas

Connecting the List.Perm abelian-square hypothesis in `g(w)` to the
Boolean spanning checks, via explicit localization and Perm → sameParikh4.

## Performance note (2025-05)

The algebraic Parikh-matrix analysis (`no_spanning_large`) now handles all
spanning lengths ≥ 7, replacing the 100+ brute-force `native_decide` files
that previously covered lengths 7–13 individually. Only the length-6
spanning check remains as a single fast `native_decide`.
-/

set_option maxHeartbeats 4000000

namespace Erdos192

/-! ### Explicit localization -/

theorem abelianSquare_localize_explicit (w : List (Fin 4))
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    let w' := w.drop a |>.take m
    (r + 2 * L ≤ (applyKeranenG w').length) ∧
    ((applyKeranenG w').drop r |>.take L).Perm
      ((applyKeranenG w').drop (r + L) |>.take L) := by
  refine' ⟨ _, _ ⟩;
  · rw [ applyKeranenG_length ] at *;
    simp +arith +decide [ List.length_take, List.length_drop ];
    omega;
  · have h_localize : List.drop i (applyKeranenG w) = List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w)) ∧ List.drop (i + L) (applyKeranenG w) = List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w)) := by
      have h_localize : ∀ (a : ℕ) (w : List (Fin 4)), List.drop (85 * a) (applyKeranenG w) = applyKeranenG (List.drop a w) := by
        intro a w; induction' a with a ih generalizing w <;> simp_all +decide [ List.drop ] ;
        rcases w <;> simp_all +decide [ Nat.mul_succ, List.drop ];
        · rfl;
        · simp_all +decide [ applyKeranenG, List.drop_append ];
          simp_all +decide [ keranenG_length ];
      rw [ ← h_localize ];
      constructor <;> rw [ List.drop_drop ] <;> congr 1 <;> omega;
    have h_localize : applyKeranenG (List.drop (i / 85) w) = applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) ++ applyKeranenG (List.drop ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) := by
      unfold applyKeranenG; simp +decide ;
      rw [ ← List.take_append_drop ( ( i + 2 * L - 1 ) / 85 - i / 85 + 1 ) ( List.drop ( i / 85 ) w ), List.flatMap_append ];
      simp +decide [ List.drop_drop ];
    have h_localize : List.take L (List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) ∧ List.take L (List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85 + L) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) := by
      rw [ h_localize ];
      rw [ List.drop_append, List.drop_append ];
      constructor <;> rw [ List.take_append_of_le_length ];
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
    lia

theorem localized_block_span (w : List (Fin 4)) (i L : ℕ) (_hL : L > 0)
    (_hlen : i + 2 * L ≤ (applyKeranenG w).length) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    (r + 2 * L - 1) / 85 + 1 = m := by
  omega

/-! ### Spanning contradiction lemmas -/

/-
No ASF word of length 6 has a spanning Perm-based abelian square.
-/
theorem no_spanning6_perm (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hw_len : w.length = 6)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = 6)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  obtain ⟨a, b, c, d, e, f, rfl⟩ : ∃ a b c d e f : Fin 4, w = [a, b, c, d, e, f] := by
    rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | ⟨ d, _ | ⟨ e, _ | ⟨ f, _ | w ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ) <;> simp_all +arith +decide;
  have h_spanning : hasSpanning6AS [a, b, c, d, e, f] = true := by
    unfold hasSpanning6AS; simp_all +decide [ List.isPerm_iff ] ;
    refine' ⟨ r, hr, L - ( ( 426 - r + 1 ) / 2 ), _, _ ⟩ <;> norm_num at *;
    · omega;
    · lia;
  exact absurd h_spanning ( by simpa using no_spanning6_abelianSquare a b c d e f ( isFinASF_complete _ hw ) )

/-! ### Main inductive block bound -/

/-- **Block bound by well-founded induction.**
For any ASF word `w`, an abelian square in `g(w)` spans at most 5 blocks.

Proved by strong induction on `w.length`:
- If `m < w.length`: extract subword `w'` of length `m`, apply IH.
- If `m = w.length ≤ 5`: trivial.
- If `m = w.length = 6`: contradiction via spanning-6 check (single `native_decide`).
- If `m = w.length ≥ 7`: contradiction via algebraic Parikh-matrix bridge. -/
theorem abelianSquare_block_bound_inductive :
    ∀ (w : List (Fin 4)), FinAbelianSquareFree w →
    ∀ (i L : ℕ), L > 0 → i + 2 * L ≤ (applyKeranenG w).length →
    ((applyKeranenG w).drop i |>.take L).Perm
      ((applyKeranenG w).drop (i + L) |>.take L) →
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5 := by
  -- Reformulate with explicit length parameter for strong induction
  suffices h : ∀ n, ∀ w : List (Fin 4), w.length ≤ n →
    FinAbelianSquareFree w →
    ∀ i L, L > 0 → i + 2 * L ≤ (applyKeranenG w).length →
    ((applyKeranenG w).drop i |>.take L).Perm
      ((applyKeranenG w).drop (i + L) |>.take L) →
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5
    from fun w hw i L hL hlen hperm => h w.length w le_rfl hw i L hL hlen hperm
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro w hw_le hw i L hL hlen hperm
    set m := (i + 2 * L - 1) / 85 - i / 85 + 1 with hm_def
    set a := i / 85 with ha_def
    set r := i % 85 with hr_def
    -- m ≤ w.length
    have ham : a + m ≤ w.length := by
      rw [applyKeranenG_length] at hlen; omega
    -- If m ≤ 5: done
    by_contra hm_gt
    push_neg at hm_gt
    -- hm_gt : 6 ≤ m
    -- Extract localization
    set w' := w.drop a |>.take m with hw'_def
    have hw' : FinAbelianSquareFree w' := finASF_subword w hw a m ham
    obtain ⟨hlen', hperm'⟩ := abelianSquare_localize_explicit w i L hL hlen hperm
    have hspan : (r + 2 * L - 1) / 85 + 1 = m := localized_block_span w i L hL hlen
    have hw'_len : w'.length = m := by
      simp [hw'_def, List.length_take, List.length_drop]; omega
    have hr_lt : r < 85 := Nat.mod_lt i (by omega)
    -- Case split: m < w.length or m = w.length
    by_cases hm_lt : m < w.length
    · -- m < w.length: apply IH to w' (which has length m < w.length ≤ n)
      have hm_lt_n : m < n := by omega
      have ih_result := ih m hm_lt_n w' (by omega) hw' r L hL hlen' hperm'
      -- ih_result : (r + 2*L - 1)/85 - r/85 + 1 ≤ 5
      -- Since r < 85: r/85 = 0
      have hr_div : r / 85 = 0 := by omega
      -- So (r+2L-1)/85 + 1 ≤ 5, i.e., m ≤ 5
      omega
    · -- m = w.length (spanning case)
      push_neg at hm_lt
      have hm_eq : m = w.length := by omega
      -- a = 0 (since a + m ≤ w.length and m = w.length)
      have ha_zero : a = 0 := by omega
      -- w' = w
      have hw'_eq_w : w' = w := by
        simp only [hw'_def, ha_zero]
        simp only [List.drop_zero]
        exact List.take_of_length_le (by omega)
      -- Simplify using i/85 = 0
      have hi85 : i / 85 = 0 := by omega
      simp only [hi85, Nat.sub_zero, List.drop_zero,
        List.take_of_length_le (by omega : w.length ≤ (i + 2 * L - 1) / 85 + 1)] at hlen' hperm'
      -- Case split: m = 6 or m ≥ 7
      rcases Nat.lt_or_ge m 7 with hm6 | hm7
      · -- m = 6: spanning-6 check
        exact no_spanning6_perm w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'
      · -- m ≥ 7: algebraic Parikh-matrix bridge
        exact no_spanning_large w hw (by omega) r L hL hr_lt hlen' (by omega) hperm'

end Erdos192

/-!
## Source: `KE92.lean`
-/


/-!
# KE92 — Keränen 1992 paper formalization

Common infrastructure for the Keränen 1992 paper workspace.  This file
re-exports every definition and helper lemma needed by the downstream
Erdős problem files (`Erdos231.lean`, `Erdos192.lean`).

## Dependency structure

- `PaperCoreDefs.lean` — shared definitions and basic lemmas (abelian-square-free,
  Parikh walk, 3-AP, Keränen morphism, boolean ASF check, subword lemmas).
- `KeranenBounded.lean`, `KeranenBounded5a–d.lean` — bounded verification by
  `native_decide` (morphism preservation for words of length ≤ 5).
- `BlockBound*.lean`, `BlockBoundBridge*.lean`, `BlockBoundSpanning*.lean` —
  Parikh-matrix finite reduction (any abelian square in the morphism image
  spans ≤ 5 letter-blocks).

## Main results proved here

- `morphism_preserves_le5` — the morphism image of any ASF word of length ≤ 5
  is abelian-square-free.
- `keranenG_preserves_ASF` — Keränen's morphism preserves abelian-square-freeness.
- `exists_finASF_all_lengths` — for every `n`, there exists a length-`n` ASF word
  on four letters.
- `exists_inf_abelianSquareFree_four` — there exists an infinite ASF word on four
  letters.
-/

set_option maxHeartbeats 4000000

namespace Erdos192

/-! ### Bounded verification for small lengths -/

/-- Morphism preservation for length 1. -/
theorem morphism_check_1 :
    ∀ a : Fin 4, isFinASF [a] = true →
    isFinASF (applyKeranenG [a]) = true := by native_decide

/-- Morphism preservation for length 2. -/
theorem morphism_check_2 :
    ∀ a b : Fin 4, isFinASF [a, b] = true →
    isFinASF (applyKeranenG [a, b]) = true := by native_decide

/-- Morphism preservation for length 3. -/
theorem morphism_check_3 :
    ∀ a b c : Fin 4, isFinASF [a, b, c] = true →
    isFinASF (applyKeranenG [a, b, c]) = true := by native_decide

/-- Combined: for any ASF word of length ≤ 5, the morphism image is ASF. -/
theorem morphism_preserves_le5 (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hlen : w.length ≤ 5) : FinAbelianSquareFree (applyKeranenG w) := by
  obtain ⟨a, b, c, d, e, hw_eq⟩ :
      ∃ a b c d e : Fin 4,
        w = [a, b, c, d, e] ∨ w = [a, b, c, d] ∨ w = [a, b, c] ∨
        w = [a, b] ∨ w = [a] ∨ w = [] := by
    rcases w with (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | w⟩⟩⟩⟩⟩) <;>
      simp_all +decide
    linarith
  rcases hw_eq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (have := isFinASF_complete _ hw; simp_all +decide only [isFinASF_sound])
  · fin_cases a <;> simp_all +decide only
    · exact isFinASF_sound _ (morphism_check_5a b c d e this)
    · exact isFinASF_sound _ (morphism_check_5b _ _ _ _ this)
    · exact isFinASF_sound _ (morphism_check_5c _ _ _ _ this)
    · exact isFinASF_sound _ (morphism_check_5d _ _ _ _ this)
  · exact isFinASF_sound _ (morphism_check_4 a b c d this)
  · exact isFinASF_sound _ (morphism_check_3 a b c this)
  · exact isFinASF_sound _ (morphism_check_2 a b this)
  · exact isFinASF_sound _ (morphism_check_1 a this)

/-! ### Abelian-square localization in uniform morphism images -/

/-- Length of `g(w.take n)` when `n ≤ w.length`. -/
private lemma applyKeranenG_take_length (w : List (Fin 4)) (n : ℕ) (hn : n ≤ w.length) :
    (applyKeranenG (w.take n)).length = 85 * n := by
  rw [applyKeranenG_length, List.length_take, Nat.min_eq_left hn]

/-- Abelian square localization for Keränen's uniform morphism.

If `applyKeranenG w` has an abelian square at position `(i, L)`, then
`applyKeranenG w'` is not abelian-square-free, where `w'` is the subword
`w.drop a |>.take m` with `a = i / 85` and `m = (i+2L−1)/85 − a + 1`. -/
private lemma abelianSquare_flatMap_localize (w : List (Fin 4))
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    ¬FinAbelianSquareFree
      (applyKeranenG (w.drop (i / 85) |>.take ((i + 2 * L - 1) / 85 - i / 85 + 1))) := by
  contrapose! hperm
  set a := i / 85
  set r := i % 85
  set m := (i + 2 * L - 1) / 85 - a + 1
  have ha : a ≤ w.length := by rw [applyKeranenG_length] at hlen; omega
  have hm : a + m ≤ w.length := by rw [applyKeranenG_length] at hlen; omega
  have hr : r + 2 * L ≤ 85 * m := by omega
  have h_split :
      applyKeranenG w =
        applyKeranenG (w.take a) ++ applyKeranenG (w.drop a |>.take m) ++
          applyKeranenG (w.drop (a + m)) := by
    have h_split : w = w.take a ++ (w.drop a |>.take m) ++ w.drop (a + m) := by
      simp +arith +decide
    unfold applyKeranenG
    simp +decide
    conv_lhs => rw [h_split, List.flatMap_append, List.flatMap_append]
    rw [List.append_assoc]
  have h_simplify :
      List.take L (List.drop i (applyKeranenG w)) =
        List.take L (List.drop r (applyKeranenG (w.drop a |>.take m))) ∧
      List.take L (List.drop (i + L) (applyKeranenG w)) =
        List.take L (List.drop (r + L) (applyKeranenG (w.drop a |>.take m))) := by
    have h1 :
        List.drop i (applyKeranenG w) =
          List.drop r
            (applyKeranenG (w.drop a |>.take m) ++ applyKeranenG (w.drop (a + m))) ∧
        List.drop (i + L) (applyKeranenG w) =
          List.drop (r + L)
            (applyKeranenG (w.drop a |>.take m) ++ applyKeranenG (w.drop (a + m))) := by
      have h2 :
          List.drop i (applyKeranenG w) =
            List.drop (i - 85 * a) (List.drop (85 * a) (applyKeranenG w)) ∧
          List.drop (i + L) (applyKeranenG w) =
            List.drop (i + L - 85 * a) (List.drop (85 * a) (applyKeranenG w)) := by
        simp +decide [List.drop_drop]
        lia
      rw [h2.1, h2.2, h_split]
      simp +decide [List.drop_append, applyKeranenG_take_length _ _ ha]
      have hir : i - 85 * a = r := by
        have hmod : r + 85 * a = i := by
          simpa [a, r] using Nat.mod_add_div i 85
        omega
      have hiLr : i + L - 85 * a = r + L := by
        have hmod : r + 85 * a = i := by
          simpa [a, r] using Nat.mod_add_div i 85
        omega
      simp +decide [hir, hiLr]
    simp_all +decide [List.drop_append, applyKeranenG_length]
    omega
  simp_all +decide [FinAbelianSquareFree]
  convert hperm r L hL _ using 1
  rw [applyKeranenG_length]
  simp +arith +decide [*]
  exact le_trans (by linarith)
    (Nat.mul_le_mul_left _
      (le_min (Nat.le_refl _) (Nat.le_sub_of_add_le (by linarith))))

/-! ### Block bound (Parikh-matrix finite reduction) -/

/-- **Block bound** (Keränen's Parikh-matrix analysis).

For any ASF word `w`, an abelian square in `applyKeranenG w` at position
`(i, L)` spans at most 5 letter-blocks. -/
private lemma abelianSquare_block_bound (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    (i + 2 * L - 1) / 85 - i / 85 + 1 ≤ 5 :=
  abelianSquare_block_bound_inductive w hw i L hL hlen hperm

/-! ### Main theorem -/

/-- **Keränen's morphism preserves abelian-square-freeness.**

Proved by:
1. **Localization** (`abelianSquare_flatMap_localize`): any abelian square in
   `g(w)` at `(i, L)` gives a non-ASF witness in `g(w')` where `w'` is a
   subword of `w`.
2. **Block bound** (`abelianSquare_block_bound`): the subword has `≤ 5`
   letters.
3. **Bounded verification** (`morphism_preserves_le5`): `g(w')` is ASF for
   all ASF `w'` with `|w'| ≤ 5`.

This yields a contradiction. -/
theorem keranenG_preserves_ASF (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    FinAbelianSquareFree (applyKeranenG w) := by
  intro i L hL hlen hperm
  set a := i / 85
  set m := (i + 2 * L - 1) / 85 - a + 1
  set w' := w.drop a |>.take m
  have ham : a + m ≤ w.length := by
    rw [applyKeranenG_length] at hlen
    have : i + 2 * L - 1 < 85 * w.length := by omega
    have : (i + 2 * L - 1) / 85 < w.length := Nat.div_lt_of_lt_mul this
    omega
  have hw'_asf : FinAbelianSquareFree w' := finASF_subword w hw a m ham
  have hw'_len : w'.length ≤ 5 := by
    have := abelianSquare_block_bound w hw i L hL hlen hperm
    simp only [w', List.length_take, List.length_drop]
    omega
  have hgw'_asf : FinAbelianSquareFree (applyKeranenG w') :=
    morphism_preserves_le5 w' hw'_asf hw'_len
  exact absurd hgw'_asf (abelianSquare_flatMap_localize w i L hL hlen hperm)

/-! ### Downstream theorems -/

private theorem keranenIterate_ASF (n : ℕ) : FinAbelianSquareFree (keranenIterate n) := by
  induction n with
  | zero => exact singleton_finASF 0
  | succ n ih => exact keranenG_preserves_ASF _ ih

/-- **Keränen 1992, computational content.** For every `n`, there exists a finite
abelian-square-free word of length `n` on four letters. -/
theorem exists_finASF_all_lengths :
    ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w := by
  intro m
  obtain ⟨n, hn⟩ : ∃ n : ℕ, m ≤ 85 ^ n :=
    ⟨m, le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by omega) m))⟩
  exact ⟨(keranenIterate n).take m,
    by rw [List.length_take, keranenIterate_length]; omega,
    finASF_prefix _ (keranenIterate_ASF n) m (by rw [keranenIterate_length]; omega)⟩

theorem exists_inf_from_all_lengths
    (hall : ∀ m : ℕ, ∃ w : List (Fin 4), w.length = m ∧ FinAbelianSquareFree w) :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f := by
  obtain ⟨f, hf⟩ :
      ∃ f : ℕ → Fin 4,
        ∀ m : ℕ, FinAbelianSquareFree (List.ofFn (fun i : Fin m => f i)) := by
    set extendable : List (Fin 4) → Prop := fun p =>
      ∀ m : ℕ, ∃ w : List (Fin 4),
        w.length = p.length + m ∧ FinAbelianSquareFree w ∧ w.take p.length = p
    have h_pigeonhole :
        ∀ p : List (Fin 4), extendable p → ∃ c : Fin 4, extendable (p ++ [c]) := by
      intro p hp
      by_contra h_contra
      push_neg at h_contra
      have h_finite :
          ∀ c : Fin 4, ∃ m : ℕ, ∀ w : List (Fin 4),
            w.length = p.length + 1 + m → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        intro c; specialize h_contra c; unfold extendable at h_contra; aesop
      obtain ⟨M, hM⟩ :
          ∃ M : ℕ, ∀ c : Fin 4, ∀ w : List (Fin 4),
            w.length = p.length + 1 + M → FinAbelianSquareFree w →
            w.take (p.length + 1) ≠ p ++ [c] := by
        choose m hm using h_finite
        use Finset.univ.sup m
        intros c w hwASF hw
        specialize hm c (w.take (p.length + 1 + m c)) ?_ ?_ <;>
          simp_all +decide [List.take_take]
        · exact Finset.le_sup (f := m) (Finset.mem_univ c)
        · exact finASF_prefix _ hw _
            (by linarith [Finset.le_sup (f := m) (Finset.mem_univ c)])
      obtain ⟨w, hw₁, hw₂, hw₃⟩ := hp (1 + M)
      have h_take : ∃ c : Fin 4, List.take (p.length + 1) w = p ++ [c] := by
        rw [← List.take_append_drop p.length w, hw₃]
        rcases x : List.drop p.length w with (_ | ⟨c, _ | ⟨d, l⟩⟩) <;>
          simp_all +decide [List.take_append]
      grind
    choose! c hc using h_pigeonhole
    have h_rec :
        ∃ f : ℕ → Fin 4, ∀ n : ℕ,
          f n = c (List.ofFn (fun i : Fin n => f i)) := by
      have h_rec :
          ∀ n : ℕ, ∃ f : ℕ → Fin 4,
            ∀ i < n, f i = c (List.ofFn (fun j : Fin i => f j)) := by
        intro n
        induction' n with n ih
        · exact ⟨fun _ => 0, by norm_num⟩
        · obtain ⟨f, hf⟩ := ih
          use fun i =>
            if i < n then f i
            else c (List.ofFn (fun j : Fin i =>
              if j.val < n then f j.val
              else c (List.ofFn (fun k : Fin j.val => f k.val))))
          grind
      choose f hf using h_rec
      have h_eq : ∀ n m : ℕ, n ≤ m → ∀ i < n, f n i = f m i := by
        intros n m hnm i hi
        induction' i using Nat.strong_induction_on with i ih
        grind +qlia
      use fun n => f (n + 1) n
      grind
    obtain ⟨f, hf⟩ := h_rec
    use f
    have h_extendable : ∀ n : ℕ, extendable (List.ofFn (fun i : Fin n => f i)) := by
      intro n
      induction' n with n ih
      · exact fun m => by
          obtain ⟨w, hw₁, hw₂⟩ := hall m
          exact ⟨w, by simpa using hw₁, hw₂, by simp +decide⟩
      · convert hc _ ih using 1
        refine' List.ext_get _ _ <;> simp +decide [← hf]
        intro i hi₁ hi₂
        rcases i with (_ | i) <;> simp +decide [List.getElem_append, List.getElem_ofFn]
        · rintro rfl; rfl
        · grind +qlia
    intro m
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := h_extendable m 0
    grind
  use f
  intro i l hl h
  have := hf (i + 2 * l)
  simp_all +decide [FinAbelianSquareFree]
  contrapose! hf
  refine ⟨i + 2 * l, i, l, hl, by linarith, ?_⟩
  convert h using 1 <;> (refine List.ext_get ?_ ?_ <;> simp +decide [infBlock] <;> omega)

/-- **Keränen 1992, Theorem 1.** There exists an infinite abelian-square-free
word over a four-letter alphabet. -/
theorem exists_inf_abelianSquareFree_four :
    ∃ f : ℕ → Fin 4, InfAbelianSquareFree f :=
  exists_inf_from_all_lengths exists_finASF_all_lengths

end Erdos192

/-!
## Source: `Erdos192.lean`
-/


/-!
# Erdős Problem 192 — Walks avoiding 3-term arithmetic progressions

## Connection to abelian squares

Given a word `f : ℕ → Fin k`, the **Parikh walk** is the sequence `V(n) ∈ ℕ^k` where
`V(n)_c` counts occurrences of letter `c` among `f(0), …, f(n−1)`. Each step of the
walk is a standard basis vector `e_{f(n)}` ("positive unit step").

Three positions `a < b < c` satisfy `V(a) + V(c) = 2 · V(b)` (a **3-term AP** in the
walk) if and only if `f` contains an abelian square at position `a` with half-length
`b − a`. Therefore, the Parikh walk is 3-AP-free if and only if `f` is
abelian-square-free.

## Main results

* `KE92.erdos_problem_192` — There exists an infinite walk in `ℕ^4` with positive
  unit steps whose sequence of visited positions contains no 3-term AP.
* `KE92.erdos_192` — Full classification: every infinite
  positive-unit-step walk in `ℤ^d` (d ≤ 3) contains a 3-term AP, while `d ≥ 4`
  admits AP-free walks.
-/

namespace Erdos192

/-! ### Classification helpers -/

/-
Completeness of `isFinASF3`: every abelian-square-free word over `Fin 3`
satisfies `isFinASF3 w = true`.
-/
private theorem isFinASF3_complete (w : List (Fin 3)) (hw : FinAbelianSquareFree w) :
    isFinASF3 w = true := by
  unfold isFinASF3;
  simp +zetaDelta at *;
  intro i hi j hj hij; contrapose! hw;
  exact fun h => h i ( j + 1 ) ( Nat.succ_pos _ ) hij ( by simpa [ List.isPerm_iff ] using hw )

/-
Infinite abelian-square-freeness is preserved under composition with
an injection.
-/
private theorem inf_asf_comp_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : ℕ → α) (e : α → β) (he : Function.Injective e)
    (hf : InfAbelianSquareFree f) : InfAbelianSquareFree (e ∘ f) := by
  intro i l hl; specialize hf i l hl; simp_all +decide
  contrapose! hf;
  rw [ ← List.map_perm_map_iff he ];
  unfold infBlock at *; aesop;

/-
No infinite word over `Fin 3` is abelian-square-free.
Proof: by `max_asf_3letters`, every length-8 prefix has an abelian square.
-/
private theorem no_inf_asf_three (f : ℕ → Fin 3) : ¬InfAbelianSquareFree f := by
  intro hf
  have h8 : FinAbelianSquareFree (infBlock f 0 8) := by
    -- For any i, l, if the two blocks of length l starting at i and i+l are permutations, then they are also permutations of the infinite word.
    intro i l hl h
    have := hf i l hl
    contrapose! this
    simp_all +decide [ infBlock ];
    convert this using 1;
    · refine' List.ext_get _ _ <;> simp +arith +decide
      omega;
    · refine' List.ext_get _ _ <;> simp +arith +decide;
      omega;
  convert isFinASF3_complete _ h8 using 1;
  simp [infBlock];
  exact max_asf_3letters _ _ _ _ _ _ _ _

/-
For `d ≤ 3`, every infinite word over `Fin d` has a Parikh AP.
-/
private theorem hasParikhAP_of_le_three {d : ℕ} (hd : d ≤ 3) (f : ℕ → Fin d) :
    hasParikhAP f := by
  -- Let `e := Fin.castLE hd : Fin d → Fin 3`. This is injective (Fin.castLE_injective).
  set e : Fin d → Fin 3 := fun x => Fin.castLE hd x
  have he_inj : Function.Injective e := by
    exact fun x y h => Fin.ext <| by simpa [ Fin.ext_iff ] using h;
  -- If `InfAbelianSquareFree f`, then by `inf_asf_comp_inj`, `InfAbelianSquareFree (e ∘ f)`.
  by_cases h_inf_asf : InfAbelianSquareFree f;
  · exact False.elim <| no_inf_asf_three ( e ∘ f ) <| inf_asf_comp_inj f e he_inj h_inf_asf;
  · exact Classical.not_not.1 fun h => h_inf_asf <| by simpa [ h ] using infAbelianSquareFree_iff_parikhAPFree f |>.2 h;

/-
For `d ≥ 4`, there exists an infinite parikhAPFree word over `Fin d`.
-/
private theorem exists_parikhAPFree_of_ge_four {d : ℕ} (hd : 4 ≤ d) :
    ∃ f : ℕ → Fin d, parikhAPFree f := by
  -- From exists_inf_abelianSquareFree_four, get f : ℕ → Fin 4 with InfAbelianSquareFree f.
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four;
  use fun n => Fin.castLE hd (f n);
  exact infAbelianSquareFree_iff_parikhAPFree _ |>.1 ( inf_asf_comp_inj f ( Fin.castLE hd ) ( Fin.castLE_injective _ ) hf )

/-- **Erdős Problem 192 — Full classification.**

An infinite walk in `ℤ^d` with positive unit steps has all its visited positions
free of 3-term arithmetic progressions if and only if `d ≥ 4`.

Equivalently, `(∀ f, hasParikhAP f) ↔ d ≤ 3`:
* **`d ≤ 3`**: every infinite word over a ≤ 3-letter alphabet contains an abelian
  square (no length-8 word over 3 letters is abelian-square-free), so every
  positive-unit-step walk in dimensions ≤ 3 has a 3-term AP.
* **`d ≥ 4`**: Keränen's 85-uniform morphism produces an infinite
  abelian-square-free word over 4 letters, giving a walk in `ℤ^4` (and hence
  in `ℤ^d` for all `d ≥ 4`) with no 3-term AP. -/
theorem erdos_192 (d : ℕ) :
    (∀ f : ℕ → Fin d, hasParikhAP f) ↔ d ≤ 3 := by
  constructor
  · intro h
    by_contra hd
    push_neg at hd
    obtain ⟨f, hf⟩ := exists_parikhAPFree_of_ge_four (by omega : 4 ≤ d)
    exact hf (h f)
  · intro hd f
    exact hasParikhAP_of_le_three hd f

#print axioms erdos_192
-- 'Erdos192.erdos_192' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]

end Erdos192
