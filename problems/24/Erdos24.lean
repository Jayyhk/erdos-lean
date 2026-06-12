/-
Released under Apache 2.0 license.
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/
import Mathlib

namespace Erdos24

-- ↓↓↓ inlined from Erdos24IntCheck.lean (kernel-decide integer verification) ↓↓↓

open Finset

/-! ### Integer certificate matrices -/

def P_int_fin (i j : Fin 8) : Int := match i.val, j.val with
  | 0, 0 => 24 | 0, 1 => -36 | 0, 2 => -36 | 0, 3 => 24 | 0, 4 => -36 | 0, 5 => 24 | 0, 6 => 24 | 0, 7 => -36
  | 1, 0 => -36 | 1, 1 => 277 | 1, 2 => 97 | 1, 3 => -79 | 1, 4 => 97 | 1, 5 => -79 | 1, 6 => -259 | 1, 7 => 54
  | 2, 0 => -36 | 2, 1 => 97 | 2, 2 => 277 | 2, 3 => -79 | 2, 4 => 97 | 2, 5 => -259 | 2, 6 => -79 | 2, 7 => 54
  | 3, 0 => 24 | 3, 1 => -79 | 3, 2 => -79 | 3, 3 => 247 | 3, 4 => -259 | 3, 5 => 67 | 3, 6 => 67 | 3, 7 => -36
  | 4, 0 => -36 | 4, 1 => 97 | 4, 2 => 97 | 4, 3 => -259 | 4, 4 => 277 | 4, 5 => -79 | 4, 6 => -79 | 4, 7 => 54
  | 5, 0 => 24 | 5, 1 => -79 | 5, 2 => -259 | 5, 3 => 67 | 5, 4 => -79 | 5, 5 => 247 | 5, 6 => 67 | 5, 7 => -36
  | 6, 0 => 24 | 6, 1 => -259 | 6, 2 => -79 | 6, 3 => 67 | 6, 4 => -79 | 6, 5 => 67 | 6, 6 => 247 | 6, 7 => -36
  | 7, 0 => -36 | 7, 1 => 54 | 7, 2 => 54 | 7, 3 => -36 | 7, 4 => 54 | 7, 5 => -36 | 7, 6 => -36 | 7, 7 => 54
  | _, _ => 0

def Q_int_fin (i j : Fin 6) : Int := match i.val, j.val with
  | 0, 0 => 1728 | 0, 1 => -1551 | 0, 2 => -1551 | 0, 3 => -1308 | 0, 4 => 687 | 0, 5 => 687
  | 1, 0 => -1551 | 1, 1 => 2336 | 1, 2 => 742 | 1, 3 => 908 | 1, 4 => 2557 | 1, 5 => -4084
  | 2, 0 => -1551 | 2, 1 => 742 | 2, 2 => 2336 | 2, 3 => 908 | 2, 4 => -4084 | 2, 5 => 2557
  | 3, 0 => -1308 | 3, 1 => 908 | 3, 2 => 908 | 3, 3 => 1728 | 3, 4 => -254 | 3, 5 => -254
  | 4, 0 => 687 | 4, 1 => 2557 | 4, 2 => -4084 | 4, 3 => -254 | 4, 4 => 15264 | 4, 5 => -14424
  | 5, 0 => 687 | 5, 1 => -4084 | 5, 2 => 2557 | 5, 3 => -254 | 5, 4 => -14424 | 5, 5 => 15264
  | _, _ => 0

def R_int_fin (i j : Fin 5) : Int := match i.val, j.val with
  | 0, 0 => 1512 | 0, 1 => 568 | 0, 2 => -380 | 0, 3 => 568 | 0, 4 => -376
  | 1, 0 => 568 | 1, 1 => 475 | 1, 2 => -191 | 1, 3 => 0 | 1, 4 => -93
  | 2, 0 => -380 | 2, 1 => -191 | 2, 2 => 192 | 2, 3 => -191 | 2, 4 => -2
  | 3, 0 => 568 | 3, 1 => 0 | 3, 2 => -191 | 3, 3 => 475 | 3, 4 => -93
  | 4, 0 => -376 | 4, 1 => -93 | 4, 2 => -2 | 4, 3 => -93 | 4, 4 => 190
  | _, _ => 0

/-! ### Flag index functions (duplicated for self-containment) -/

def σ₀FI (adjDA adjDB adjDC : Bool) : Fin 8 :=
  ⟨(if adjDA then 1 else 0) + (if adjDB then 2 else 0) + (if adjDC then 4 else 0),
   by cases adjDA <;> cases adjDB <;> cases adjDC <;> simp⟩

def σ₁FI (adjDA adjDB adjDC : Bool) : Option (Fin 6) :=
  match adjDA, adjDB, adjDC with
  | false, false, false => some 0 | true, false, false => some 1
  | false, true, false => some 2 | false, false, true => some 3
  | true, false, true => some 4 | false, true, true => some 5
  | _, _, _ => none

def σ₂FI (adjDA adjDCenter adjDC : Bool) : Option (Fin 5) :=
  match adjDA, adjDCenter, adjDC with
  | false, false, false => some 0 | true, false, false => some 1
  | false, true, false => some 2 | false, false, true => some 3
  | true, false, true => some 4
  | _, _, _ => none

/-! ### Integer quintuple contribution (= 2500 × quintContrib) -/

/-- Integer version of `quintContrib`, equal to `2500 * quintContrib adj p`. -/
def intQC (adj : Fin 5 → Fin 5 → Bool) (p : Equiv.Perm (Fin 5)) : Int :=
  let a := p 0; let b := p 1; let c := p 2; let d := p 3; let e := p 4
  let ab := adj a b; let ac := adj a c; let bc := adj b c
  if !ab && !ac && !bc then
    4 * P_int_fin (σ₀FI (adj d a) (adj d b) (adj d c))
                  (σ₀FI (adj e a) (adj e b) (adj e c))
  else if ab && !ac && !bc then
    match σ₁FI (adj d a) (adj d b) (adj d c),
          σ₁FI (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => Q_int_fin fi fj
    | _, _ => 0
  else if ab && bc && !ac then
    match σ₂FI (adj d a) (adj d b) (adj d c),
          σ₂FI (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => 4 * R_int_fin fi fj
    | _, _ => 0
  else 0

/-! ### Nat-encoded graph adjacency -/

def getBitN (n i : Nat) : Bool := (n >>> i) &&& 1 == 1

def adj5N (n : Nat) : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 => getBitN n 0 | 0, 2 | 2, 0 => getBitN n 1
  | 0, 3 | 3, 0 => getBitN n 2 | 0, 4 | 4, 0 => getBitN n 3
  | 1, 2 | 2, 1 => getBitN n 4 | 1, 3 | 3, 1 => getBitN n 5
  | 1, 4 | 4, 1 => getBitN n 6 | 2, 3 | 3, 2 => getBitN n 7
  | 2, 4 | 4, 2 => getBitN n 8 | 3, 4 | 4, 3 => getBitN n 9
  | _, _ => false

def isTriFreeN (n : Nat) : Bool :=
  let g := adj5N n
  let chk (a b c : Fin 5) := !(g a b && g b c && g a c)
  chk 0 1 2 && chk 0 1 3 && chk 0 1 4 && chk 0 2 3 && chk 0 2 4 &&
  chk 0 3 4 && chk 1 2 3 && chk 1 2 4 && chk 1 3 4 && chk 2 3 4

def isC5N (n : Nat) : Bool :=
  let g := adj5N n
  let deg (v : Fin 5) : Nat :=
    (if g v 0 then 1 else 0) + (if g v 1 then 1 else 0) +
    (if g v 2 then 1 else 0) + (if g v 3 then 1 else 0) +
    (if g v 4 then 1 else 0)
  deg 0 == 2 && deg 1 == 2 && deg 2 == 2 && deg 3 == 2 && deg 4 == 2

/-! ### Range check utility -/

def checkRangeN (f : Nat → Bool) (lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => f (lo + n) && checkRangeN f lo n

theorem checkRangeN_sound (f : Nat → Bool) (lo n : Nat)
    (h : checkRangeN f lo n = true) : ∀ k, k < n → f (lo + k) = true := by
  induction n with
  | zero => intro k hk; omega
  | succ m ih =>
    intro k hk
    simp [checkRangeN, Bool.and_eq_true] at h
    by_cases hkm : k = m
    · exact hkm ▸ h.1
    · exact ih h.2 k (by omega)

/-! ### Kernel-verified decide proofs -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000000 in
theorem intCheck_flag_bound :
    checkRangeN (fun n => !isTriFreeN n || decide
      (Finset.univ.sum (fun p => intQC (adj5N n) p) ≤ 11520)) 0 1024 = true := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000000 in
theorem intCheck_flag_bound_c5 :
    checkRangeN (fun n => !isTriFreeN n || decide
      (Finset.univ.sum (fun p => intQC (adj5N n) p) +
        (if isC5N n then 300000 else 0) ≤ 11520)) 0 1024 = true := by
  decide

-- ↑↑↑ end inlined Erdos24IntCheck ↑↑↑

/-!
# Erdős Pentagon Conjecture

We prove that every triangle-free graph on `5n` vertices contains at most `n⁵` copies
of the 5-cycle `C₅`, settling the Erdős pentagon conjecture in the affirmative.

## Main results

- `erdos_24`: Every triangle-free graph on `5n` vertices has ≤ `n⁵`
  copies of `C₅`.

## Proof outline

Following Grzesik (2012), the proof proceeds in two steps:

1. **Flag algebra bound** (`flag_algebra_c5_turan_density`):
   The Turán density of `C₅` in `K₃`-free graphs satisfies `π_{C₅}(K₃) ≤ 24/625`,
   proved via Razborov's flag algebra method with explicit semidefinite certificates.

2. **Blow-up argument** (`erdos_24`):
   Given a triangle-free graph `G` on `5n` vertices with `c = numC5Copies G` copies of
   `C₅`, its balanced blow-up `G.blowup N` is triangle-free with at least `c · N⁵` copies.
   Applying the Turán density bound with `ε = 12/(625·n⁵)` to the blow-up (for `N` large
   enough) yields `c ≤ n⁵ + 1/2`, hence `c ≤ n⁵`.

## References

* A. Grzesik, *On the maximum number of five-cycles in a triangle-free graph*,
  J. Combin. Theory Ser. B, 102(5):1061–1066, 2012.
* A. Razborov, *Flag algebras*, J. Symbolic Logic, 72(4):1239–1282, 2007.
* H. Hatami, J. Hladký, D. Král', S. Norine, A. Razborov,
  *On the number of pentagons in triangle-free graphs*, J. Combin. Theory Ser. A,
  120(3):722–732, 2013.
-/

open Finset Function SimpleGraph Fintype Nat Matrix

attribute [local instance] Classical.propDecidable

/-!
## § 1. Certificate Matrices and PSD Verification

Three certificate matrices P (8×8), Q (6×6), R (5×5) from the flag algebra proof,
verified positive semidefinite via explicit LDLᵀ decompositions checked by `decide`.
-/

/-- Certificate matrix P (8×8) for type σ₀, scaled by 625. -/
def P_cert : Matrix (Fin 8) (Fin 8) ℚ := !![
  24, -36, -36, 24, -36, 24, 24, -36;
  -36, 277, 97, -79, 97, -79, -259, 54;
  -36, 97, 277, -79, 97, -259, -79, 54;
  24, -79, -79, 247, -259, 67, 67, -36;
  -36, 97, 97, -259, 277, -79, -79, 54;
  24, -79, -259, 67, -79, 247, 67, -36;
  24, -259, -79, 67, -79, 67, 247, -36;
  -36, 54, 54, -36, 54, -36, -36, 54]

/-- Certificate matrix Q (6×6) for type σ₁, scaled by 2500. -/
def Q_cert : Matrix (Fin 6) (Fin 6) ℚ := !![
  1728, -1551, -1551, -1308, 687, 687;
  -1551, 2336, 742, 908, 2557, -4084;
  -1551, 742, 2336, 908, -4084, 2557;
  -1308, 908, 908, 1728, -254, -254;
  687, 2557, -4084, -254, 15264, -14424;
  687, -4084, 2557, -254, -14424, 15264]

/-- Certificate matrix R (5×5) for type σ₂, scaled by 625. -/
def R_cert : Matrix (Fin 5) (Fin 5) ℚ := !![
  1512, 568, -380, 568, -376;
  568, 475, -191, 0, -93;
  -380, -191, 192, -191, -2;
  568, 0, -191, 475, -93;
  -376, -93, -2, -93, 190]

private def L_P : Matrix (Fin 8) (Fin 8) ℚ := !![
  1, 0, 0, 0, 0, 0, 0, 0;
  -3/2, 1, 0, 0, 0, 0, 0, 0;
  -3/2, 43/223, 1, 0, 0, 0, 0, 0;
  1, -43/223, -43/266, 1, 0, 0, 0, 0;
  -3/2, 43/223, 43/266, -1, 1, 0, 0, 0;
  1, -43/223, -1, 0, 0, 1, 0, 0;
  1, -1, 0, 0, 0, 0, 1, 0;
  -3/2, 0, 0, 0, 0, 0, 0, 1]

private def D_P_vec : Fin 8 → ℚ :=
  ![24, 223, 47880/223, 27810/133, 0, 0, 0, 0]

private def L_Q : Matrix (Fin 6) (Fin 6) ℚ := !![
  1, 0, 0, 0, 0, 0;
  -517/576, 1, 0, 0, 0, 0;
  -517/576, -124825/181223, 1, 0, 0, 0;
  -109/144, -51076/181223, -25538/28199, 1, 0, 0;
  229/576, 609337/181223, -8235/3188, 0, 1, 0;
  229/576, -95105/25889, 5047/3188, 0, -1, 1]

private def D_Q_vec : Fin 6 → ℚ :=
  ![1728, 181223/192, 89898412/181223, 7221232/28199, 3219791/3188, 0]

private def L_R : Matrix (Fin 5) (Fin 5) ℚ := !![
  1, 0, 0, 0, 0;
  71/189, 1, 0, 0, 0;
  -95/378, -9119/49447, 1, 0, 0;
  71/189, -40328/49447, -1, 1, 0;
  -47/189, 9119/49447, -1, 0, 1]

private def D_R_vec : Fin 5 → ℚ :=
  ![1512, 49447/189, 4331525/49447, 0, 0]

set_option maxHeartbeats 6400000 in
private lemma P_ldlt : P_cert = L_P * Matrix.diagonal D_P_vec * L_P.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [P_cert, L_P, D_P_vec, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.vecHead, Matrix.vecTail] <;>
  norm_num

set_option maxHeartbeats 6400000 in
private lemma Q_ldlt : Q_cert = L_Q * Matrix.diagonal D_Q_vec * L_Q.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [Q_cert, L_Q, D_Q_vec, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.vecHead, Matrix.vecTail] <;>
  norm_num

set_option maxHeartbeats 3200000 in
private lemma R_ldlt : R_cert = L_R * Matrix.diagonal D_R_vec * L_R.transpose := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [R_cert, L_R, D_R_vec, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.vecHead, Matrix.vecTail] <;>
  norm_num

private lemma D_P_nonneg : ∀ i : Fin 8, 0 ≤ D_P_vec i := by
  intro i; fin_cases i <;> simp [D_P_vec, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num

private lemma D_Q_nonneg : ∀ i : Fin 6, 0 ≤ D_Q_vec i := by
  intro i; fin_cases i <;> simp [D_Q_vec, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num

private lemma D_R_nonneg : ∀ i : Fin 5, 0 ≤ D_R_vec i := by
  intro i; fin_cases i <;> simp [D_R_vec, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num

/-- If `M = L * diag(d) * Lᵀ` with `d ≥ 0`, then `M` is positive semidefinite. -/
lemma psd_of_ldlt {n : ℕ} (M L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (hd : ∀ i, 0 ≤ d i)
    (hM : M = L * Matrix.diagonal d * L.transpose) :
    ∀ v : Fin n → ℚ, 0 ≤ dotProduct v (M.mulVec v) := by
  intro v
  have : v ⬝ᵥ (M *ᵥ v) =
      (Lᵀ *ᵥ v) ⬝ᵥ (Matrix.diagonal d *ᵥ (Lᵀ *ᵥ v)) := by
    simp [hM, Matrix.mul_assoc, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  simp_all [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_nonneg fun i _ => by nlinarith [hd i, mul_self_nonneg ((Lᵀ *ᵥ v) i)]

lemma P_cert_psd : ∀ v : Fin 8 → ℚ, 0 ≤ dotProduct v (P_cert.mulVec v) :=
  psd_of_ldlt P_cert L_P D_P_vec D_P_nonneg P_ldlt

lemma Q_cert_psd : ∀ v : Fin 6 → ℚ, 0 ≤ dotProduct v (Q_cert.mulVec v) :=
  psd_of_ldlt Q_cert L_Q D_Q_vec D_Q_nonneg Q_ldlt

lemma R_cert_psd : ∀ v : Fin 5 → ℚ, 0 ≤ dotProduct v (R_cert.mulVec v) :=
  psd_of_ldlt R_cert L_R D_R_vec D_R_nonneg R_ldlt

/-!
## § 2. Flag Indices and Contributions
-/

/-- Flag index for type σ₀ (no edges among labeled triple). -/
def σ₀FlagIdx (adjDA adjDB adjDC : Bool) : Fin 8 :=
  ⟨(if adjDA then 1 else 0) + (if adjDB then 2 else 0) + (if adjDC then 4 else 0),
   by cases adjDA <;> cases adjDB <;> cases adjDC <;> simp⟩

/-- Flag index for type σ₁ (edge between first two labeled vertices). -/
def σ₁FlagIdx (adjDA adjDB adjDC : Bool) : Option (Fin 6) :=
  match adjDA, adjDB, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | false, true, true => some 5
  | _, _, _ => none

/-- Flag index for type σ₂ (path through center vertex). -/
def σ₂FlagIdx (adjDA adjDCenter adjDC : Bool) : Option (Fin 5) :=
  match adjDA, adjDCenter, adjDC with
  | false, false, false => some 0
  | true, false, false => some 1
  | false, true, false => some 2
  | false, false, true => some 3
  | true, false, true => some 4
  | _, _, _ => none

/-- Contribution of one ordered quintuple to the flag algebra sum. -/
def quintContrib (adj : Fin 5 → Fin 5 → Bool) (p : Equiv.Perm (Fin 5)) : ℚ :=
  let a := p 0; let b := p 1; let c := p 2; let d := p 3; let e := p 4
  let ab := adj a b; let ac := adj a c; let bc := adj b c
  if !ab && !ac && !bc then
    P_cert (σ₀FlagIdx (adj d a) (adj d b) (adj d c))
           (σ₀FlagIdx (adj e a) (adj e b) (adj e c)) / 625
  else if ab && !ac && !bc then
    match σ₁FlagIdx (adj d a) (adj d b) (adj d c),
          σ₁FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => Q_cert fi fj / 2500
    | _, _ => 0
  else if ab && bc && !ac then
    match σ₂FlagIdx (adj d a) (adj d b) (adj d c),
          σ₂FlagIdx (adj e a) (adj e b) (adj e c) with
    | some fi, some fj => R_cert fi fj / 625
    | _, _ => 0
  else 0

/-- Total flag contribution for a graph on `Fin 5`. -/
def totalFlagContrib (adj : Fin 5 → Fin 5 → Bool) : ℚ :=
  (Finset.univ : Finset (Equiv.Perm (Fin 5))).sum (fun p => quintContrib adj p)

/-!
## § 3. Computational Bound Verification
-/

/-- Encode a graph on `Fin 5` as a function from edge indices to `Bool`. -/
def mkAdj5 (e : Fin 10 → Bool) : Fin 5 → Fin 5 → Bool := fun i j =>
  match i.val, j.val with
  | 0, 1 | 1, 0 => e 0 | 0, 2 | 2, 0 => e 1 | 0, 3 | 3, 0 => e 2 | 0, 4 | 4, 0 => e 3
  | 1, 2 | 2, 1 => e 4 | 1, 3 | 3, 1 => e 5 | 1, 4 | 4, 1 => e 6
  | 2, 3 | 3, 2 => e 7 | 2, 4 | 4, 2 => e 8 | 3, 4 | 4, 3 => e 9
  | _, _ => false

/-! ### Bridge lemmas connecting integer and rational computations -/

private lemma σ₀FI_eq : σ₀FI = σ₀FlagIdx := by
  ext a b c; simp [σ₀FI, σ₀FlagIdx]

private lemma σ₁FI_eq : σ₁FI = σ₁FlagIdx := by
  ext a b c; cases a <;> cases b <;> cases c <;> rfl

private lemma σ₂FI_eq : σ₂FI = σ₂FlagIdx := by
  ext a b c; cases a <;> cases b <;> cases c <;> rfl

set_option maxHeartbeats 6400000 in
private lemma P_cert_eq_int : ∀ i j : Fin 8, P_cert i j = (P_int_fin i j : ℚ) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [P_cert, P_int_fin]

set_option maxHeartbeats 3200000 in
private lemma Q_cert_eq_int : ∀ i j : Fin 6, Q_cert i j = (Q_int_fin i j : ℚ) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [Q_cert, Q_int_fin]

set_option maxHeartbeats 1600000 in
private lemma R_cert_eq_int : ∀ i j : Fin 5, R_cert i j = (R_int_fin i j : ℚ) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [R_cert, R_int_fin]

private lemma quintContrib_eq_intQC_div (adj : Fin 5 → Fin 5 → Bool)
    (p : Equiv.Perm (Fin 5)) :
    quintContrib adj p = (intQC adj p : ℚ) / 2500 := by
  unfold quintContrib intQC;
  rw [ show σ₀FI = σ₀FlagIdx from σ₀FI_eq, show σ₁FI = σ₁FlagIdx from σ₁FI_eq, show σ₂FI = σ₂FlagIdx from σ₂FI_eq ];
  rw [ show P_cert = _ from funext fun i => funext fun j => P_cert_eq_int i j ] ; rw [ show Q_cert = _ from funext fun i => funext fun j => Q_cert_eq_int i j ] ; rw [ show R_cert = _ from funext fun i => funext fun j => R_cert_eq_int i j ] ;
  cases h : σ₁FlagIdx ( adj ( p 3 ) ( p 0 ) ) ( adj ( p 3 ) ( p 1 ) ) ( adj ( p 3 ) ( p 2 ) ) <;> cases h' : σ₁FlagIdx ( adj ( p 4 ) ( p 0 ) ) ( adj ( p 4 ) ( p 1 ) ) ( adj ( p 4 ) ( p 2 ) ) <;> simp +decide [ h, h' ] at *;
  · split_ifs <;> first | ring1 | ring_nf;
    cases h : σ₂FlagIdx ( adj ( p 3 ) ( p 0 ) ) ( adj ( p 3 ) ( p 1 ) ) ( adj ( p 3 ) ( p 2 ) ) <;> cases h' : σ₂FlagIdx ( adj ( p 4 ) ( p 0 ) ) ( adj ( p 4 ) ( p 1 ) ) ( adj ( p 4 ) ( p 2 ) ) <;> simp +decide [ h, h' ] at *;
    ring;
  · split_ifs <;> first | ring1 | ring_nf;
    cases h : σ₂FlagIdx ( adj ( p 3 ) ( p 0 ) ) ( adj ( p 3 ) ( p 1 ) ) ( adj ( p 3 ) ( p 2 ) ) <;> cases h' : σ₂FlagIdx ( adj ( p 4 ) ( p 0 ) ) ( adj ( p 4 ) ( p 1 ) ) ( adj ( p 4 ) ( p 2 ) ) <;> simp +decide [ h, h' ] at *;
    ring;
  · split_ifs <;> first | ring1 | ring_nf;
    cases h : σ₂FlagIdx ( adj ( p 3 ) ( p 0 ) ) ( adj ( p 3 ) ( p 1 ) ) ( adj ( p 3 ) ( p 2 ) ) <;> cases h' : σ₂FlagIdx ( adj ( p 4 ) ( p 0 ) ) ( adj ( p 4 ) ( p 1 ) ) ( adj ( p 4 ) ( p 2 ) ) <;> simp +decide [ h, h' ] at *;
    ring;
  · cases h : σ₂FlagIdx ( adj ( p 3 ) ( p 0 ) ) ( adj ( p 3 ) ( p 1 ) ) ( adj ( p 3 ) ( p 2 ) ) <;> cases h' : σ₂FlagIdx ( adj ( p 4 ) ( p 0 ) ) ( adj ( p 4 ) ( p 1 ) ) ( adj ( p 4 ) ( p 2 ) ) <;> simp +decide [ h, h' ] at *;
    · split_ifs <;> ring;
    · split_ifs <;> ring;
    · split_ifs <;> ring;
    · grind

private lemma totalFlagContrib_eq_intSum_div (adj : Fin 5 → Fin 5 → Bool) :
    totalFlagContrib adj =
      ((Finset.univ : Finset (Equiv.Perm (Fin 5))).sum (fun p => intQC adj p) : ℚ) / 2500 := by
  unfold totalFlagContrib
  simp_rw [quintContrib_eq_intQC_div]
  rw [Finset.sum_div]

/-- Encode `Fin 10 → Bool` as a natural number in `[0, 1024)`. -/
def encodeGraph (e : Fin 10 → Bool) : Nat :=
  (if e 0 then 1 else 0) + (if e 1 then 2 else 0) + (if e 2 then 4 else 0) +
  (if e 3 then 8 else 0) + (if e 4 then 16 else 0) + (if e 5 then 32 else 0) +
  (if e 6 then 64 else 0) + (if e 7 then 128 else 0) + (if e 8 then 256 else 0) +
  (if e 9 then 512 else 0)

private lemma encodeGraph_lt (e : Fin 10 → Bool) : encodeGraph e < 1024 := by
  simp only [encodeGraph]; split <;> split <;> split <;> split <;> split <;>
    split <;> split <;> split <;> split <;> split <;> omega

set_option maxHeartbeats 6400000 in
private lemma encodeGraph_eq_bit (e : Fin 10 → Bool) :
    encodeGraph e = Nat.bit (e 0) (Nat.bit (e 1) (Nat.bit (e 2) (Nat.bit (e 3)
      (Nat.bit (e 4) (Nat.bit (e 5) (Nat.bit (e 6) (Nat.bit (e 7)
        (Nat.bit (e 8) (Nat.bit (e 9) 0))))))))) := by
  simp only [encodeGraph, Nat.bit_val]
  cases e 0 <;> cases e 1 <;> cases e 2 <;> cases e 3 <;> cases e 4 <;>
    cases e 5 <;> cases e 6 <;> cases e 7 <;> cases e 8 <;> cases e 9 <;>
    simp [Bool.toNat]

private lemma getBitN_eq_testBit (n i : Nat) : getBitN n i = n.testBit i := by
  simp [getBitN, Nat.testBit]

private lemma getBitN_encode (e : Fin 10 → Bool) (i : Fin 10) :
    getBitN (encodeGraph e) i.val = e i := by
  rw [getBitN_eq_testBit, encodeGraph_eq_bit]
  fin_cases i <;> simp [Nat.testBit_bit_succ]

private lemma adj5N_encode (e : Fin 10 → Bool) :
    adj5N (encodeGraph e) = mkAdj5 e := by
  ext i j;
  fin_cases i <;> fin_cases j <;> simp +decide [adj5N, mkAdj5];
  all_goals exact getBitN_encode e ⟨ _, by decide ⟩ ;

private lemma isTriFreeN_of_triFree (e : Fin 10 → Bool)
    (h : ∀ a b c : Fin 5, ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) :
    isTriFreeN (encodeGraph e) = true := by
  simp only [isTriFreeN, adj5N_encode]
  simp +zetaDelta at *;
  grind +locals

/-
For every triangle-free graph on `Fin 5`,
`totalFlagContrib ≤ 576/125 = 120 · (24/625)`.
Checked over all `2^10 = 1024` possible edge configurations.
-/
theorem flag_bound_all_graphs : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) ≤ 576 / 125 := by
  intro e htf
  rw [totalFlagContrib_eq_intSum_div]
  have hlt := encodeGraph_lt e
  have hadj := adj5N_encode e
  have htfN := isTriFreeN_of_triFree e htf
  have hcheck := checkRangeN_sound _ 0 1024 intCheck_flag_bound (encodeGraph e) hlt
  simp [htfN, hadj] at hcheck
  convert div_le_div_of_nonneg_right ( Int.cast_le.mpr hcheck ) ( by norm_num : ( 0 : ℚ ) ≤ 2500 ) using 1 ; norm_num [ Finset.sum_div _ _ _ ];
  norm_num [ div_eq_mul_inv ]

-- bridge from Int bound to ℚ bound

/-- Whether a graph on `Fin 5` is a 5-cycle (every vertex has degree exactly 2). -/
def isC5_adj (adj : Fin 5 → Fin 5 → Bool) : Bool :=
  ((Finset.univ : Finset (Fin 5)).filter (fun v =>
    ((Finset.univ : Finset (Fin 5)).filter (fun w => adj v w)).card = 2)).card = 5

set_option maxHeartbeats 40000000 in
private lemma isC5N_eq (e : Fin 10 → Bool) :
    isC5N (encodeGraph e) = isC5_adj (mkAdj5 e) := by
  have he : e = ![e 0, e 1, e 2, e 3, e 4, e 5, e 6, e 7, e 8, e 9] := by
    ext k; fin_cases k <;> rfl
  rw [he]
  cases e 0 <;> cases e 1 <;> cases e 2 <;> cases e 3 <;> cases e 4 <;>
    cases e 5 <;> cases e 6 <;> cases e 7 <;> cases e 8 <;> cases e 9 <;>
    decide

/-
Strengthened computational bound including the C₅ indicator.
-/
theorem flag_bound_with_c5 : ∀ e : Fin 10 → Bool,
    (∀ a b c : Fin 5,
      ¬(mkAdj5 e a b = true ∧ mkAdj5 e b c = true ∧ mkAdj5 e a c = true)) →
    totalFlagContrib (mkAdj5 e) +
      120 * (if isC5_adj (mkAdj5 e) then 1 else 0) ≤ 576 / 125 := by
  intro e htf
  rw [totalFlagContrib_eq_intSum_div, ← isC5N_eq]
  have hlt := encodeGraph_lt e
  have hadj := adj5N_encode e
  have htfN := isTriFreeN_of_triFree e htf
  have hcheck := checkRangeN_sound _ 0 1024 intCheck_flag_bound_c5 (encodeGraph e) hlt
  simp [htfN, hadj] at hcheck
  convert div_le_div_of_nonneg_right ( Int.cast_le.mpr hcheck ) ( by norm_num : ( 0 : ℚ ) ≤ 2500 ) using 1 ; norm_num [ Finset.sum_ite ] ; ring_nf!;
  · grind;
  · norm_num

/-!
## § 4. Graph Adjacency from Injective Functions
-/

/-- The adjacency function of `G` pulled back along `f : Fin 5 → V`. -/
noncomputable def graphAdj5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    Fin 5 → Fin 5 → Bool :=
  fun i j => decide (G.Adj (f i) (f j))

lemma graphAdj5_symm {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i j, graphAdj5 G f i j = graphAdj5 G f j i := by
  intro i j; unfold graphAdj5; simp [G.adj_comm]

lemma graphAdj5_irrefl {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    ∀ i, graphAdj5 G f i i = false := by
  intro i; unfold graphAdj5; simp

set_option maxHeartbeats 800000 in
lemma graphAdj5_triangleFree {V : Type*}
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (f : Fin 5 → V) (_hf : f.Injective) :
    ∀ a b c : Fin 5,
      ¬(graphAdj5 G f a b = true ∧ graphAdj5 G f b c = true ∧
        graphAdj5 G f a c = true) := by
  contrapose! hG
  unfold graphAdj5 at *
  simp [SimpleGraph.cliqueFree_iff] at *
  obtain ⟨a, b, hab, c, hbc, hac⟩ := hG
  refine ⟨⟨fun x => if x = 0 then f a else if x = 1 then f b else f c, ?_⟩, ?_⟩
  · simp [Function.Injective, Fin.forall_fin_succ]
    exact ⟨⟨hab.ne, hac.ne⟩, ⟨hab.symm.ne, hbc.ne⟩, hac.symm.ne, hbc.symm.ne⟩
  · simp [Fin.forall_fin_succ, hab, hbc, hac, SimpleGraph.adj_comm]

/-!
## § 5. Connecting `graphAdj5` to `mkAdj5`
-/

/-- Extract edge bits from an adjacency function. -/
def toEdges5 (adj : Fin 5 → Fin 5 → Bool) : Fin 10 → Bool :=
  ![adj 0 1, adj 0 2, adj 0 3, adj 0 4, adj 1 2,
    adj 1 3, adj 1 4, adj 2 3, adj 2 4, adj 3 4]

lemma mkAdj5_toEdges5 (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false) :
    mkAdj5 (toEdges5 adj) = adj := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [*, mkAdj5, toEdges5]
  · exact hsym _ _
  · exact hsym _ _

lemma flag_bound_for_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj ≤ 576 / 125 := by
  rw [show adj = mkAdj5 (toEdges5 adj) from (mkAdj5_toEdges5 adj hsym hirr).symm]
  exact flag_bound_all_graphs (toEdges5 adj) (by rwa [mkAdj5_toEdges5 adj hsym hirr])

lemma flag_bound_with_c5_adj (adj : Fin 5 → Fin 5 → Bool)
    (hsym : ∀ i j, adj i j = adj j i)
    (hirr : ∀ i, adj i i = false)
    (htf : ∀ a b c : Fin 5,
      ¬(adj a b = true ∧ adj b c = true ∧ adj a c = true)) :
    totalFlagContrib adj +
      120 * (if isC5_adj adj then 1 else 0) ≤ 576 / 125 := by
  rw [show adj = mkAdj5 (toEdges5 adj) from (mkAdj5_toEdges5 adj hsym hirr).symm]
  exact flag_bound_with_c5 (toEdges5 adj) (by rwa [mkAdj5_toEdges5 adj hsym hirr])

/-!
## § 6. Equivariance of `quintContrib`
-/

lemma totalFlagContrib_perm_inv (adj : Fin 5 → Fin 5 → Bool)
    (τ : Equiv.Perm (Fin 5)) :
    totalFlagContrib (fun i j => adj (τ i) (τ j)) = totalFlagContrib adj := by
  refine Finset.sum_bij (fun σ _ => τ * σ) ?_ ?_ ?_ ?_
  all_goals simp [Equiv.Perm.ext_iff]
  · exact fun b => ⟨τ.symm * b, fun x => by simp⟩
  · exact fun a => Rat.ext rfl rfl

/-!
## § 7. PSD Non-negativity of Quadratic Form
-/

/-- PSD double sum lemma: if `M` is PSD then `∑_{d,e} M(flag d, flag e) ≥ 0`. -/
lemma sum_sum_psd_nonneg {k : ℕ} {M : Matrix (Fin k) (Fin k) ℚ}
    (hM : ∀ v : Fin k → ℚ, 0 ≤ dotProduct v (M.mulVec v))
    {α : Type*} (S : Finset α) (flag : α → Fin k) :
    (0 : ℚ) ≤ S.sum fun d => S.sum fun e => M (flag d) (flag e) := by
  convert hM _
  swap
  exact fun i => (S.filter fun x => flag x = i).card
  · simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    have : ∑ d ∈ S, ∑ e ∈ S, M (flag d) (flag e) =
        ∑ i, ∑ d ∈ S.filter (fun x => flag x = i),
          ∑ j, ∑ e ∈ S.filter (fun x => flag x = j), M i j := by
      simp only [Finset.sum_sigma']
      exact Finset.sum_bij (fun x _ => ⟨flag x.fst, x.fst, flag x.snd, x.snd⟩)
        (by aesop) (by aesop) (by aesop) (by aesop)
    simp_all [mul_comm, mul_left_comm, Finset.mul_sum]

set_option maxHeartbeats 800000 in
lemma sum_sum_psd_option {k : ℕ} {M : Matrix (Fin k) (Fin k) ℚ}
    (hM : ∀ v : Fin k → ℚ, 0 ≤ dotProduct v (M.mulVec v))
    {α : Type*} (S : Finset α) (flag : α → Option (Fin k)) (scale : ℚ)
    (hscale : 0 < scale) :
    (0 : ℚ) ≤ S.sum fun d => S.sum fun e =>
      match flag d, flag e with
      | some fi, some fj => M fi fj / scale
      | _, _ => 0 := by
  have h_nonneg : 0 ≤ ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
      M i j * (∑ d ∈ S, if flag d = some i then 1 else 0) *
        (∑ e ∈ S, if flag e = some j then 1 else 0) := by
    convert hM (fun i => ∑ d ∈ S, if flag d = some i then 1 else 0) using 1
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
  have h_sum : ∑ d ∈ S, ∑ e ∈ S,
      (match flag d, flag e with
      | some fi, some fj => M fi fj / scale
      | _, _ => 0) =
      ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
        M i j / scale *
          (∑ d ∈ S, if flag d = some i then 1 else 0) *
          (∑ e ∈ S, if flag e = some j then 1 else 0) := by
    have : ∑ d ∈ S, ∑ e ∈ S,
        (match flag d, flag e with
        | some fi, some fj => M fi fj / scale
        | _, _ => 0) =
        ∑ d ∈ S, ∑ e ∈ S, ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ,
          (if flag d = some i then M i j / scale else 0) *
          (if flag e = some j then 1 else 0) := by
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
      cases flag d <;> cases flag e <;> simp
    convert this using 1
    simp only [Finset.mul_sum, sum_mul, mul_assoc]
    simp only [Finset.sum_sigma']
    refine' Finset.sum_bij (fun x _ =>
        ⟨x.snd.snd.snd, x.snd.snd.fst, x.fst, x.snd.fst⟩) _ _ _ _
      <;> simp
    · exact fun a ha₁ ha₂ => ⟨ha₂, ha₁⟩
    · bound
    · exact fun b hb₁ hb₂ => ⟨_, _, _, _, ⟨hb₂, hb₁⟩, rfl⟩
  exact h_sum.symm ▸ by
    simpa only [div_mul_eq_mul_div, Finset.sum_div] using div_nonneg h_nonneg hscale.le

lemma quintContrib_type0 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = false) (h02 : adj 0 2 = false) (h12 : adj 1 2 = false) :
    quintContrib adj (Equiv.refl _) =
      P_cert (σ₀FlagIdx (adj 3 0) (adj 3 1) (adj 3 2))
             (σ₀FlagIdx (adj 4 0) (adj 4 1) (adj 4 2)) / 625 := by
  simp [quintContrib, h01, h02, h12]

lemma quintContrib_type1 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = true) (h02 : adj 0 2 = false) (h12 : adj 1 2 = false) :
    quintContrib adj (Equiv.refl _) =
      match σ₁FlagIdx (adj 3 0) (adj 3 1) (adj 3 2),
            σ₁FlagIdx (adj 4 0) (adj 4 1) (adj 4 2) with
      | some fi, some fj => Q_cert fi fj / 2500
      | _, _ => 0 := by
  simp [quintContrib, h01, h02, h12]

lemma quintContrib_type2 (adj : Fin 5 → Fin 5 → Bool)
    (h01 : adj 0 1 = true) (h12 : adj 1 2 = true) (h02 : adj 0 2 = false) :
    quintContrib adj (Equiv.refl _) =
      match σ₂FlagIdx (adj 3 0) (adj 3 1) (adj 3 2),
            σ₂FlagIdx (adj 4 0) (adj 4 1) (adj 4 2) with
      | some fi, some fj => R_cert fi fj / 625
      | _, _ => 0 := by
  simp [quintContrib, h01, h12, h02]

set_option maxHeartbeats 800000 in
/-- The quadratic form `∑_{d,e} quintContrib(![a,b,c,d,e])` is non-negative. -/
lemma quadForm_nonneg {V : Type*} [Fintype V]
    (G : SimpleGraph V) (a b c : V) :
    (0 : ℚ) ≤ (Finset.univ : Finset V).sum fun d =>
      (Finset.univ : Finset V).sum fun e =>
        quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) := by
  by_cases h_ab : G.Adj a b
  · by_cases h_ac : G.Adj a c
    · unfold quintContrib; simp [*, graphAdj5]
    · by_cases h_bc : G.Adj b c
      · convert sum_sum_psd_option R_cert_psd (Finset.univ : Finset V)
            (fun d => σ₂FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2)) 625 (by norm_num) using 1
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [quintContrib_type2]
        · unfold graphAdj5; simp
          congr! 1; ext
          cases ‹Option (Fin 5)› <;> cases ‹Option (Fin 5)› <;> rfl
        · unfold graphAdj5; aesop
        · unfold graphAdj5; aesop
        · unfold graphAdj5; aesop
      · convert sum_sum_psd_option Q_cert_psd (Finset.univ : Finset V)
            (fun d => σ₁FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2)) 2500 (by norm_num) using 1
        refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
        rw [quintContrib_type1]
        · unfold graphAdj5; simp
          congr! 1; ext
          cases ‹Option (Fin 6)› <;> cases ‹Option (Fin 6)› <;> rfl
        · unfold graphAdj5; aesop
        · unfold graphAdj5; aesop
        · unfold graphAdj5; aesop
  · by_cases h_ac : G.Adj a c <;> by_cases h_bc : G.Adj b c
    · unfold quintContrib; simp [*, graphAdj5]
    · unfold quintContrib; simp [*, graphAdj5]
    · unfold quintContrib; simp [*, graphAdj5]
    · have h_eq : ∀ d e : V,
          quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) =
            P_cert (σ₀FlagIdx (graphAdj5 G ![a, b, c, d, e] 3 0)
                    (graphAdj5 G ![a, b, c, d, e] 3 1)
                    (graphAdj5 G ![a, b, c, d, e] 3 2))
                   (σ₀FlagIdx (graphAdj5 G ![a, b, c, d, e] 4 0)
                    (graphAdj5 G ![a, b, c, d, e] 4 1)
                    (graphAdj5 G ![a, b, c, d, e] 4 2)) / 625 := by
        intro d e
        apply quintContrib_type0 <;> unfold graphAdj5 <;> aesop
      simp_rw [h_eq]
      convert mul_nonneg (inv_nonneg.mpr (show (625 : ℚ) ≥ 0 by norm_num))
          (sum_sum_psd_nonneg P_cert_psd (Finset.univ : Finset V)
            (fun d => σ₀FlagIdx (graphAdj5 G ![a, b, c, d, d] 3 0)
              (graphAdj5 G ![a, b, c, d, d] 3 1)
              (graphAdj5 G ![a, b, c, d, d] 3 2))) using 1
      simp only [inv_mul_eq_div, sum_div]
      unfold graphAdj5; simp

/-!
## § 8. Bounds on `quintContrib` Values
-/

/-
Every `quintContrib` value is ≤ 7 (verified computationally).
-/
private lemma P_entry_le : ∀ i j : Fin 8, P_cert i j / 625 ≤ 7 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [P_cert] <;> norm_num

private lemma Q_entry_le : ∀ i j : Fin 6, Q_cert i j / 2500 ≤ 7 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [Q_cert] <;> norm_num

private lemma R_entry_le : ∀ i j : Fin 5, R_cert i j / 625 ≤ 7 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [R_cert] <;> norm_num

theorem quintContrib_le_seven :
    ∀ (e : Fin 10 → Bool), quintContrib (mkAdj5 e) (Equiv.refl _) ≤ 7 := by
  intro e
  unfold quintContrib
  simp only [Equiv.refl_apply]
  split_ifs with h1 h2 h3
  · exact P_entry_le _ _
  · match σ₁FlagIdx (mkAdj5 e 3 0) (mkAdj5 e 3 1) (mkAdj5 e 3 2),
          σ₁FlagIdx (mkAdj5 e 4 0) (mkAdj5 e 4 1) (mkAdj5 e 4 2) with
    | some fi, some fj => exact Q_entry_le fi fj
    | some _, none | none, some _ | none, none => norm_num
  · match σ₂FlagIdx (mkAdj5 e 3 0) (mkAdj5 e 3 1) (mkAdj5 e 3 2),
          σ₂FlagIdx (mkAdj5 e 4 0) (mkAdj5 e 4 1) (mkAdj5 e 4 2) with
    | some fi, some fj => exact R_entry_le fi fj
    | some _, none | none, some _ | none, none => norm_num
  · norm_num

/-- `quintContrib` is bounded by 7 for any `graphAdj5`. -/
lemma quintContrib_le_for_graphAdj {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) :
    quintContrib (graphAdj5 G f) (Equiv.refl _) ≤ 7 := by
  rw [show graphAdj5 G f = mkAdj5 (toEdges5 (graphAdj5 G f))
    from (mkAdj5_toEdges5 (graphAdj5 G f) (graphAdj5_symm G f) (graphAdj5_irrefl G f)).symm]
  exact quintContrib_le_seven _

/-!
## § 9. PSD Lower Bound on Injective Sum
-/

/-- The global sum over all functions `f : Fin 5 → V` is non-negative. -/
lemma allFuncSum_nonneg {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (0 : ℚ) ≤ (Finset.univ : Finset (Fin 5 → V)).sum
      fun f => quintContrib (graphAdj5 G f) (Equiv.refl _) := by
  have h_decomp : ∑ f : Fin 5 → V,
      quintContrib (graphAdj5 G f) (Equiv.refl _) =
      ∑ a : V, ∑ b : V, ∑ c : V, ∑ d : V, ∑ e : V,
        quintContrib (graphAdj5 G ![a, b, c, d, e]) (Equiv.refl _) := by
    simp only [← sum_product']
    refine Finset.sum_bij (fun f _ => (f 0, f 1, f 2, f 3, f 4)) ?_ ?_ ?_ ?_
    all_goals simp
    · exact fun a₁ a₂ h₀ h₁ h₂ h₃ h₄ =>
        funext fun i => by fin_cases i <;> assumption
    · exact fun a b c d e =>
        ⟨fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c
          else if i = 3 then d else e, rfl, rfl, rfl, rfl, rfl⟩
    · intro a; congr; ext i; fin_cases i <;> rfl
  exact h_decomp.symm ▸
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun c _ => quadForm_nonneg G a b c

set_option maxHeartbeats 800000 in
/-- Number of non-injective functions `Fin 5 → V` is at most `10 * n^4`. -/
lemma non_injective_count_le {V : Type*} [Fintype V] :
    ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).card ≤
      10 * Fintype.card V ^ 4 := by
  suffices ∀ n : ℕ,
      ((Finset.univ : Finset (Fin 5 → Fin n)).filter fun f => ¬f.Injective).card ≤
        10 * n ^ 4 by
    obtain ⟨e⟩ : Nonempty (V ≃ Fin (Fintype.card V)) := ⟨Fintype.equivFin V⟩
    convert this (Fintype.card V) using 1
    refine' Finset.card_bij (fun f _ i => e (f i)) _ _ _ <;>
      simp +decide [Function.Injective]
    · exact fun a₁ x y hxy hne a₂ u v huv hne' h =>
        funext fun i => e.injective <| congr_fun h i
    · exact fun b x y hxy hne =>
        ⟨fun i => e.symm (b i), ⟨x, y, by simpa using hxy, hne⟩, by simp +decide⟩
  intro n
  by_cases hn : n ≤ 4
  · set_option maxRecDepth 8192 in set_option maxHeartbeats 6400000 in interval_cases n <;> decide
  · have h_count :
        (Finset.univ.filter fun f : Fin 5 → Fin n => Injective f).card =
          Nat.descFactorial n 5 := by
      have h_eq : (Finset.univ.filter fun f : Fin 5 → Fin n => Injective f) =
          Finset.image (fun f : Fin 5 ↪ Fin n => f.toFun)
            (Finset.univ : Finset (Fin 5 ↪ Fin n)) := by
        ext f; simp [Function.Injective]
        exact ⟨fun h => ⟨⟨f, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.injective⟩
      rw [h_eq, Finset.card_image_of_injective _
          (fun f g h => by simpa [Function.Injective] using h)]
      simp +decide [Finset.card_univ]
    rw [Finset.filter_not, Finset.card_sdiff]
    simp_all [Finset.card_univ]
    zify
    have h_pow2 := pow_pos (by linarith : 0 < n) 2
    have h_pow3 := pow_pos (by linarith : 0 < n) 3
    rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_sub, Nat.cast_sub] <;>
      (try push_cast) <;> nlinarith

/-- PSD lower bound: `∑_{f injective} quintContrib ≥ -70 * n^4`. -/
lemma psd_lower_bound_injective {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (-(70 : ℚ) * (Fintype.card V : ℚ) ^ 4) ≤
      ((Finset.univ : Finset (Fin 5 → V)).filter fun f => f.Injective).sum
        fun f => quintContrib (graphAdj5 G f) (Equiv.refl _) := by
  have h_split := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 5 → V)) (fun f => f.Injective)
    (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _))
  have h_all := allFuncSum_nonneg G
  have h_bound :
      ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
        (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _)) ≤
        70 * (Fintype.card V : ℚ) ^ 4 := by
    calc ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
            (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _))
        ≤ ((Finset.univ : Finset (Fin 5 → V)).filter fun f => ¬f.Injective).sum
            fun _ => (7 : ℚ) := by
          apply Finset.sum_le_sum
          intro f _
          exact_mod_cast quintContrib_le_for_graphAdj G f
      _ = 7 * ((Finset.univ : Finset (Fin 5 → V)).filter fun f =>
            ¬f.Injective).card := by
          simp [Finset.sum_const, mul_comm]
      _ ≤ 7 * (10 * Fintype.card V ^ 4) := by
          exact_mod_cast Nat.mul_le_mul_left 7 (non_injective_count_le (V := V))
      _ = 70 * (Fintype.card V : ℚ) ^ 4 := by ring
  linarith

/-!
## § 10. Counting Identity
-/

set_option maxHeartbeats 1600000 in
/-- The sum of `quintContrib` over injective functions equals the sum of
`totalFlagContrib` over 5-element subsets. -/
lemma counting_identity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (enum : ∀ (S : Finset V), S.card = 5 → (Fin 5 → V))
    (henum : ∀ S hS, Function.Injective (enum S hS) ∧
      Finset.image (enum S hS) Finset.univ = S) :
    ((Finset.univ : Finset (Fin 5 → V)).filter fun f => f.Injective).sum
      (fun f => quintContrib (graphAdj5 G f) (Equiv.refl _)) =
    ((Finset.univ : Finset (Finset V)).filter fun S => S.card = 5).sum
      fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (enum S h))
        else 0 := by
  have h_partition :
      ∑ f ∈ Finset.filter (fun f : Fin 5 → V => f.Injective) Finset.univ,
        quintContrib (graphAdj5 G f) (Equiv.refl _) =
      ∑ S ∈ Finset.powersetCard 5 (Finset.univ : Finset V),
        ∑ f ∈ Finset.filter
          (fun f : Fin 5 → V => f.Injective ∧ Finset.image f Finset.univ = S)
          Finset.univ,
          quintContrib (graphAdj5 G f) (Equiv.refl _) := by
    rw [← Finset.sum_biUnion]
    · rcongr f
      simp
      exact fun hf => by rw [Finset.card_image_of_injective _ hf, Finset.card_fin]
    · exact fun S _ T _ hST =>
        Finset.disjoint_left.mpr fun f hfS hfT => hST <| by aesop
  rw [h_partition, Finset.powersetCard_eq_filter]
  refine Finset.sum_congr rfl ?_
  intro S hS
  have h_bij :
      Finset.filter (fun f : Fin 5 → V =>
        f.Injective ∧ Finset.image f Finset.univ = S) Finset.univ =
      Finset.image (fun σ : Equiv.Perm (Fin 5) =>
        fun i => enum S (by simpa using hS) (σ i))
        (Finset.univ : Finset (Equiv.Perm (Fin 5))) := by
    ext f
    simp
    constructor
    · intro h
      have h_bij : ∀ i : Fin 5, ∃ j : Fin 5,
          enum S (by simpa using hS) j = f i := by
        intro i
        have : f i ∈ S :=
          h.2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have := (henum S (by simpa using hS)).2
        rw [Finset.ext_iff] at this
        grind
      choose σ hσ using h_bij
      have hσ_inj : Function.Injective σ := fun i j hij =>
        h.1 <| by have := hσ i; have := hσ j; aesop
      exact ⟨Equiv.ofBijective σ ⟨hσ_inj,
        Finite.injective_iff_surjective.mp hσ_inj⟩, funext hσ⟩
    · rintro ⟨σ, rfl⟩
      specialize henum S (by simpa using hS)
      simp [Function.Injective, Finset.ext_iff] at henum ⊢
      exact ⟨fun a₁ a₂ h => σ.injective (henum.1 h),
        fun a => ⟨fun ⟨i, hi⟩ => henum.2 a |>.1 ⟨_, hi⟩,
          fun ha => by
            obtain ⟨i, hi⟩ := henum.2 a |>.2 ha
            exact ⟨σ.symm i, by simpa using hi⟩⟩⟩
  have hScard : S.card = 5 := by simpa using hS
  simp_all +decide [Function.Injective]
  rw [Finset.sum_image
    (fun σ _ τ _ h => Equiv.Perm.ext fun i =>
      (henum S hScard).1 (by simpa using congr_fun h i))]
  unfold totalFlagContrib
  congr 1

/-!
## § 11. C₅ Copy Detection

### Counting conventions

There are two natural ways to count 5-cycles in a graph:

1. **`numC5`** (correct in general): counts labeled 5-cycles modulo the dihedral
   symmetry group D₅ (rotations and reflections), i.e. the number of
   *subgraphs* isomorphic to C₅. Formally, `numC5 G` is the number of
   labeled 5-cycles `(Fin 5 → V)` divided by 10 (= |D₅|). For example,
   `numC5 K₅ = 12` and `numC5 C₅ = 1`.

2. **`numC5Copies`** (correct only for triangle-free graphs): counts *vertex sets*
   `S : Finset V` that support at least one 5-cycle. In a triangle-free graph
   each such vertex set supports a unique cycle (up to dihedral symmetry),
   so `numC5Copies = numC5`. In general graphs, a single 5-vertex set may
   support multiple distinct 5-cycles, so `numC5Copies` undercounts.
   For instance, `numC5Copies K₅ = 1` (there is only one 5-element subset),
   whereas `numC5 K₅ = 12`.

The main theorem (`erdos_24`) is stated using `numC5` (the
correct general definition); the proof goes through `numC5Copies` via the
equivalence `numC5_eq_numC5Copies_of_triangleFree`.
-/

/-- A function `f : Fin 5 → V` defines a **labeled 5-cycle** in `G` if it is injective
and maps consecutive vertices (cyclically) to adjacent vertices. -/
def IsLabeledC5 {V : Type*} (G : SimpleGraph V) (f : Fin 5 → V) : Prop :=
  Function.Injective f ∧ ∀ i : Fin 5, G.Adj (f i) (f (i + 1))

/-- The number of 5-cycles in `G`, counting each cycle once.

A **5-cycle** is a subgraph of `G` isomorphic to the cycle graph C₅. We
formalize this as the number of labeled 5-cycles (injective maps
`f : Fin 5 → V` with `G.Adj (f i) (f (i+1))` for all `i`) divided by 10,
the order of the dihedral group D₅ = ⟨rotation, reflection⟩ that acts
freely on such labelings.

This is the correct definition for arbitrary graphs. For example,
`numC5 C₅ = 1` and `numC5 K₅ = 12`.

See also `numC5Copies` for a simpler definition that agrees with `numC5`
when the graph is triangle-free (`numC5_eq_numC5Copies_of_triangleFree`). -/
noncomputable def numC5 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → V)).filter (fun f => IsLabeledC5 G f)).card / 10

/-- A `Finset V` is a **C₅ copy** in `G` if its elements can be cyclically ordered
so that consecutive elements are adjacent.

**Warning:** This counts *vertex sets*, not *cycles*. A single 5-vertex set
can support multiple distinct 5-cycles in a general graph, so this definition
undercounts. For example, `K₅` has `numC5Copies = 1` but `numC5 = 12`.

In a triangle-free graph, the cycle through any such vertex set is unique
(up to dihedral symmetry), so `numC5Copies = numC5`; see
`numC5_eq_numC5Copies_of_triangleFree`. -/
def IsC5Copy {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ f : Fin 5 → V, IsLabeledC5 G f ∧ Finset.image f Finset.univ = s

/-- The number of 5-element vertex sets supporting a 5-cycle in `G`.

**Warning:** This is *not* the number of 5-cycles in general — it only counts
vertex sets, ignoring multiplicity when a vertex set supports several distinct
cycles. It equals the correct count `numC5` when `G` is triangle-free; see
`numC5_eq_numC5Copies_of_triangleFree`.

Used internally in the flag-algebra machinery where the triangle-free
hypothesis is always available. -/
noncomputable def numC5Copies {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  ((Finset.univ : Finset (Finset V)).filter (IsC5Copy G)).card

set_option maxHeartbeats 1600000 in
/-- If `S` is a C₅ copy in a triangle-free graph, then the induced adjacency
on any enumeration of `S` satisfies `isC5_adj`. -/
lemma isC5Copy_implies_isC5_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (S : Finset V) (enumS : Fin 5 → V) (henumInj : Function.Injective enumS)
    (henumImg : Finset.image enumS Finset.univ = S)
    (hC5 : IsC5Copy G S) :
    isC5_adj (graphAdj5 G enumS) = true := by
  obtain ⟨f, hf_inj, hf_image⟩ := hC5
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin 5), enumS = f ∘ τ := by
    have h_bij : ∀ (s : Finset V), s.card = 5 →
        ∀ g : Fin 5 → V, Function.Injective g →
        Finset.image g Finset.univ = s →
        ∀ h : Fin 5 → V, Function.Injective h →
        Finset.image h Finset.univ = s →
        ∃ τ : Equiv.Perm (Fin 5), g = h ∘ τ := by
      intro s _ g hg_inj hg_image h hh_inj hh_image
      have : ∀ x : Fin 5, ∃ y : Fin 5, h y = g x := by
        intro x
        have : g x ∈ s := hg_image ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
        exact Finset.mem_image.mp (hh_image.symm ▸ this) |>.imp fun _ => And.right
      choose τ hτ using this
      have hτ_inj : Function.Injective τ := fun x y hxy =>
        hg_inj <| by have := hτ x; have := hτ y; aesop
      exact ⟨Equiv.ofBijective τ
        ⟨hτ_inj, Finite.injective_iff_surjective.mp hτ_inj⟩,
        funext fun x => hτ x ▸ rfl⟩
    have hcard : S.card = 5 := by
      rw [← henumImg]
      exact Finset.card_image_of_injective _ henumInj
    exact h_bij _ hcard _ henumInj henumImg _ hf_inj.1 (by
      convert hf_image using 2)
  have h_deg : ∀ i, (Finset.univ.filter fun j => graphAdj5 G f i j).card = 2 := by
    have h_cycle : ∀ i : Fin 5,
        G.Adj (f i) (f (i + 1)) ∧ G.Adj (f i) (f (i - 1)) := by
      intro i
      exact ⟨hf_inj.2 i, by have := hf_inj.2 (i - 1); fin_cases i <;> tauto⟩
    have h_no_tri : ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k →
        ¬(G.Adj (f i) (f j) ∧ G.Adj (f j) (f k) ∧ G.Adj (f i) (f k)) := by
      intro i j k _ _ _ h
      have := hG {f i, f j, f k}
      simp [SimpleGraph.is3Clique_iff] at this
      exact this _ _ h.1 _ h.2.2 h.2.1 rfl
    intro i
    have h_only_neighbors : ∀ j : Fin 5,
        j ≠ i → j ≠ i + 1 → j ≠ i - 1 → ¬G.Adj (f i) (f j) := by
      all_goals have := h_cycle 0; have := h_cycle 1; have := h_cycle 2
      all_goals have := h_cycle 3; have := h_cycle 4
      all_goals simp [SimpleGraph.adj_comm] at *
      all_goals grind
    rw [Finset.card_eq_two]
    use i + 1, i - 1
    simp [Finset.ext_iff, graphAdj5]
    exact ⟨by fin_cases i <;> trivial,
      fun j => ⟨fun hj => Classical.or_iff_not_imp_left.2 fun hj' =>
          Classical.not_not.1 fun hj'' =>
            h_only_neighbors j (by aesop) (by aesop) (by aesop) hj,
        fun hj => by rcases hj with rfl | rfl
                     · exact (h_cycle i).1
                     · exact (h_cycle i).2⟩⟩
  have h_deg_enum : ∀ i,
      (Finset.univ.filter fun j => graphAdj5 G (f ∘ ⇑τ) i j).card = 2 := by
    intro i
    have : (Finset.univ.filter fun j => graphAdj5 G (f ∘ ⇑τ) i j).card =
        (Finset.univ.filter fun j => graphAdj5 G f (τ i) (τ j)).card := by
      simp [graphAdj5]
    rw [this, ← h_deg (τ i)]
    rw [Finset.card_filter, Finset.card_filter]
    conv_rhs => rw [← Equiv.sum_comp τ]
  unfold isC5_adj; aesop

/-!
## § 12. Per-subset Bound and Assembly
-/

/-- Canonical enumeration of a 5-element set. -/
noncomputable def chooseEnum5 {V : Type*} (S : Finset V) (hS : S.card = 5) :
    Fin 5 → V :=
  fun i => ((Fintype.equivFin ↥S).symm (Fin.cast (by simp [Fintype.card_coe, hS]) i)).val

lemma chooseEnum5_injective {V : Type*} (S : Finset V) (hS : S.card = 5) :
    Function.Injective (chooseEnum5 S hS) := by
  intro i j h
  simp only [chooseEnum5] at h
  exact Fin.cast_injective _
    ((Fintype.equivFin ↥S).symm.injective (Subtype.val_injective h))

lemma chooseEnum5_image {V : Type*} [DecidableEq V] (S : Finset V)
    (hS : S.card = 5) :
    Finset.image (chooseEnum5 S hS) Finset.univ = S := by
  ext x; simp only [chooseEnum5, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin ↥S).symm _).prop
  · intro hx
    exact ⟨Fin.cast (by simp [Fintype.card_coe, hS]) ((Fintype.equivFin ↥S) ⟨x, hx⟩),
           by simp [Equiv.symm_apply_apply]⟩

lemma chooseEnum5_spec {V : Type*} [DecidableEq V] (S : Finset V)
    (hS : S.card = 5) :
    Function.Injective (chooseEnum5 S hS) ∧
    Finset.image (chooseEnum5 S hS) Finset.univ = S :=
  ⟨chooseEnum5_injective S hS, chooseEnum5_image S hS⟩

lemma per_subset_c5_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (S : Finset V) (_hS : S.card = 5) (enumS : Fin 5 → V)
    (hinj : Function.Injective enumS) (himg : Finset.image enumS univ = S) :
    totalFlagContrib (graphAdj5 G enumS) +
      120 * (if IsC5Copy G S then (1 : ℚ) else 0) ≤ 576 / 125 := by
  have hc5 := flag_bound_with_c5_adj (graphAdj5 G enumS)
    (graphAdj5_symm G enumS) (graphAdj5_irrefl G enumS)
    (graphAdj5_triangleFree G hG enumS hinj)
  by_cases hcopy : IsC5Copy G S
  · simp [hcopy]
    have := isC5Copy_implies_isC5_adj G hG S enumS hinj himg hcopy
    simp [this] at hc5
    linarith
  · simp [hcopy]
    exact flag_bound_for_adj (graphAdj5 G enumS)
      (graphAdj5_symm G enumS) (graphAdj5_irrefl G enumS)
      (graphAdj5_triangleFree G hG enumS hinj)

lemma isC5Copy_card {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (h : IsC5Copy G S) : S.card = 5 := by
  obtain ⟨f, ⟨hfinj, _⟩, himg⟩ := h
  conv_lhs => rw [show S = Finset.image f Finset.univ from
    Subsingleton.elim (Classical.decEq V) ‹DecidableEq V› ▸ himg.symm]
  exact Finset.card_image_of_injective _ hfinj

lemma c5_indicator_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    ((univ : Finset (Finset V)).filter fun S => S.card = 5).sum
      (fun S => if IsC5Copy G S then (1 : ℚ) else 0) = numC5Copies G := by
  simp only [sum_boole, Nat.cast_inj]
  unfold numC5Copies
  congr 1; ext S
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨isC5Copy_card G S h, h⟩⟩

set_option maxHeartbeats 800000 in
/-- **Key intermediate bound**:
`numC5Copies ≤ (24/625) * C(n,5) + 8 * n^4`. -/
theorem numC5Copies_le_turan_plus_error {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (numC5Copies G : ℝ) ≤
      (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
      8 * (Fintype.card V : ℝ) ^ 4 := by
  set F := (univ : Finset (Finset V)).filter (fun S => S.card = 5) with hF_def
  have h_lb : -(70 : ℚ) * (Fintype.card V : ℚ) ^ 4 ≤
      F.sum fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (chooseEnum5 S h)) else 0 := by
    calc -(70 : ℚ) * _ ≤ _ := psd_lower_bound_injective G
      _ = _ := by convert counting_identity G chooseEnum5
                    fun S hS => chooseEnum5_spec S hS
  have h_step1 : F.sum (fun S => if h : S.card = 5
        then totalFlagContrib (graphAdj5 G (chooseEnum5 S h)) else 0) ≤
      F.sum fun S => (576 / 125 : ℚ) - 120 * if IsC5Copy G S then 1 else 0 := by
    apply Finset.sum_le_sum
    intro S hS
    have hScard : S.card = 5 := by simp [hF_def] at hS; exact hS
    simp only [dif_pos hScard]
    linarith [per_subset_c5_bound G hG S hScard (chooseEnum5 S hScard)
      (chooseEnum5_injective S hScard) (chooseEnum5_image S hScard)]
  have hcard : F.card = (Fintype.card V).choose 5 := by
    rw [hF_def,
      show (Finset.univ : Finset (Finset V)).filter (fun S => S.card = 5) =
        (Finset.univ : Finset V).powersetCard 5 from by ext S; simp [Finset.mem_powersetCard]]
    simp [Finset.card_powersetCard]
  have h_step2 :
      F.sum (fun S => (576 / 125 : ℚ) - 120 * if IsC5Copy G S then 1 else 0) =
      (576 / 125 : ℚ) * (Fintype.card V).choose 5 - 120 * (numC5Copies G : ℚ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum, c5_indicator_sum G, hcard]
    ring
  have hq : (numC5Copies G : ℚ) ≤
      (24 / 625 : ℚ) * (Fintype.card V).choose 5 +
        8 * (Fintype.card V : ℚ) ^ 4 := by
    have : (0 : ℚ) ≤ (Fintype.card V : ℚ) ^ 4 := by positivity
    linarith
  have h_cast := Rat.cast_le (K := ℝ) |>.mpr hq
  simp only [Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_div] at h_cast
  convert h_cast using 1

/-!
## § 13. Error Bound and Turán Density
-/

/-- For `n ≥ N₀`, the error term `8 · n⁴` is at most `ε · C(n,5)`. -/
lemma error_le_eps_choose {n : ℕ} {eps : ℝ} (heps : 0 < eps)
    (hn : n ≥ Nat.ceil (15360 * eps⁻¹ + 8)) :
    8 * (n : ℝ) ^ 4 ≤ eps * ((n.choose 5 : ℕ) : ℝ) := by
  have hn_ge_8 : 8 ≤ n :=
    le_trans (Nat.le_of_lt_succ <| by
      rw [← @Nat.cast_lt ℝ]; push_cast
      linarith [Nat.le_ceil (15360 * eps⁻¹ + 8), inv_pos.2 heps]) hn
  have hepsn_ge_15360 : 15360 ≤ eps * n := by
    nlinarith [Nat.ceil_le.mp hn, mul_inv_cancel₀ heps.ne']
  have h_prod_ge_half_pow :
      (n - 1 : ℝ) * (n - 2) * (n - 3) * (n - 4) ≥ (n / 2) ^ 4 := by
    nlinarith only [show (n : ℝ) ≥ 8 by norm_cast, sq (n - 8 : ℝ)]
  have h_binom : (Nat.choose n 5 : ℝ) =
      n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
    rw [Nat.cast_choose] <;> try linarith
    rcases n with (_ | _ | _ | _ | _ | n) <;> norm_num [Nat.factorial] at *
    rw [div_eq_div_iff] <;> first | positivity | push_cast [Nat.factorial_succ]; ring
  nlinarith [pow_pos (by positivity : 0 < (n : ℝ)) 2,
             pow_pos (by positivity : 0 < (n : ℝ)) 3,
             pow_pos (by positivity : 0 < (n : ℝ)) 4]

/-- **Turán density bound** (Theorem 1 of Grzesik, 2012).

For any `ε > 0`, all sufficiently large triangle-free graphs `G` satisfy
`numC5Copies G ≤ (24/625 + ε) · C(|V(G)|, 5)`. -/
theorem flag_algebra_c5_turan_density :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V],
      Fintype.card V ≥ N₀ → ∀ G : SimpleGraph V, G.CliqueFree 3 →
        (numC5Copies G : ℝ) ≤ (24 / 625 + ε) * ((Fintype.card V).choose 5 : ℝ) := by
  intro ε hε
  use Nat.ceil (15360 * ε⁻¹ + 8)
  intro V _ hn G hG
  have h1 := numC5Copies_le_turan_plus_error G hG
  have h2 := error_le_eps_choose hε hn
  calc (numC5Copies G : ℝ)
      ≤ (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
        8 * (Fintype.card V : ℝ) ^ 4 := h1
    _ ≤ (24 / 625 : ℝ) * ((Fintype.card V).choose 5 : ℝ) +
        ε * ((Fintype.card V).choose 5 : ℝ) := by linarith
    _ = (24 / 625 + ε) * ((Fintype.card V).choose 5 : ℝ) := by ring

/-!
## § 14. Blow-up Construction
-/

/-- **Balanced blow-up**: replace each vertex of `G` by `N` independent copies.
Two copies `(u, i)` and `(v, j)` are adjacent iff `G.Adj u v`. -/
def blowup {V : Type*} (G : SimpleGraph V) (N : ℕ) :
    SimpleGraph (V × Fin N) where
  Adj p q := G.Adj p.1 q.1
  symm _ _ h := G.symm h
  loopless := ⟨fun p h => (G.loopless).irrefl p.1 h⟩

/-- A blow-up of a `K_k`-free graph is `K_k`-free. -/
lemma blowup_cliqueFree {V : Type*} {G : SimpleGraph V}
    {k : ℕ} (hG : G.CliqueFree k) (N : ℕ) :
    (blowup G N).CliqueFree k := by
  intro s ⟨hclique, hcard⟩
  apply hG (s.image Prod.fst)
  constructor
  · intro x hx y hy hne
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hy
    exact hclique hx' hy' (fun h => hne (congr_arg Prod.fst h ▸ rfl))
  · rw [Finset.card_image_of_injOn, hcard]
    intro x hx y hy hfst
    by_contra hne
    have hadj := hclique hx hy hne
    simp [blowup] at hadj
    rw [hfst] at hadj
    exact (G.loopless).irrefl _ hadj

/-- Each labeled C₅ and function `a : Fin 5 → Fin N` give rise to a C₅ copy
in `G.blowup N`. -/
lemma blowup_IsC5Copy_of_IsLabeledC5 {V : Type*} {G : SimpleGraph V}
    {N : ℕ} {f : Fin 5 → V} (hf : IsLabeledC5 G f) (a : Fin 5 → Fin N) :
    IsC5Copy (blowup G N) (Finset.image (fun i => (f i, a i)) Finset.univ) := by
  refine ⟨fun i => (f i, a i), ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · simp [Prod.mk.injEq] at hij
    exact hf.1 hij.1
  · exact hf.2 i
  · grind

/-- Canonical witness ordering for a C₅ copy. -/
noncomputable def IsC5Copy.witness {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : IsC5Copy G s) : Fin 5 → V :=
  hs.choose

lemma IsC5Copy.witness_isLabeledC5 {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : IsC5Copy G s) : IsLabeledC5 G hs.witness :=
  hs.choose_spec.1

lemma IsC5Copy.witness_image {V : Type*} {G : SimpleGraph V}
    {s : Finset V} (hs : IsC5Copy G s) :
    Finset.image hs.witness Finset.univ = s :=
  hs.choose_spec.2

/-- The blow-up map sends `(s, a)` to the corresponding C₅ copy in `G.blowup N`. -/
noncomputable def blowupC5Map {V : Type*} (G : SimpleGraph V)
    (N : ℕ) (p : Finset V × (Fin 5 → Fin N)) : Finset (V × Fin N) :=
  if h : IsC5Copy G p.1 then
    Finset.image (fun i => (h.witness i, p.2 i)) Finset.univ
  else ∅

/-- The blow-up map sends C₅ copies in `G` to C₅ copies in `G.blowup N`. -/
lemma blowupC5Map_isC5Copy {V : Type*} {G : SimpleGraph V}
    {N : ℕ} {s : Finset V} {a : Fin 5 → Fin N} (hs : IsC5Copy G s) :
    IsC5Copy (blowup G N) (blowupC5Map G N (s, a)) := by
  simp only [blowupC5Map, dif_pos hs]
  exact blowup_IsC5Copy_of_IsLabeledC5 hs.witness_isLabeledC5 a

set_option maxHeartbeats 800000 in
/-- The blow-up map is injective on C₅ copies. -/
lemma blowupC5Map_injective {V : Type*} {G : SimpleGraph V} {N : ℕ}
    {s₁ s₂ : Finset V} {a₁ a₂ : Fin 5 → Fin N}
    (hs₁ : IsC5Copy G s₁) (hs₂ : IsC5Copy G s₂)
    (h : blowupC5Map G N (s₁, a₁) = blowupC5Map G N (s₂, a₂)) :
    s₁ = s₂ ∧ a₁ = a₂ := by
  unfold blowupC5Map at h
  have hs : s₁ = s₂ := by
    rw [← hs₁.witness_image, ← hs₂.witness_image]
    ext x
    simp_all [Finset.ext_iff]
    exact ⟨fun ⟨i, hi⟩ => by
        obtain ⟨j, hj₁, hj₂⟩ := h _ (a₁ i) |>.1 ⟨i, hi, rfl⟩
        exact ⟨j, hj₁⟩,
      fun ⟨i, hi⟩ => by
        obtain ⟨j, hj₁, hj₂⟩ := h _ (a₂ i) |>.2 ⟨i, hi, rfl⟩
        exact ⟨j, hj₁⟩⟩
  simp_all [Finset.ext_iff]
  ext i
  specialize h (hs₂.witness i) (a₁ i)
  simp_all [Function.Injective.eq_iff
    (show Function.Injective hs₂.witness from hs₂.witness_isLabeledC5.1)]

/-- The blow-up `G.blowup N` contains at least `G.numC5Copies * N ^ 5` copies of C₅. -/
lemma blowup_numC5Copies_ge {V : Type*} [Fintype V]
    {G : SimpleGraph V} {N : ℕ} (_ : 0 < N) :
    numC5Copies G * N ^ 5 ≤ numC5Copies (blowup G N) := by
  trans
  · convert Set.ncard_le_ncard (show
        Set.image (fun p : Finset V × (Fin 5 → Fin N) => blowupC5Map G N p)
          ({s : Finset V | IsC5Copy G s} ×ˢ Set.univ) ⊆
            {s : Finset (V × Fin N) | IsC5Copy (blowup G N) s}
        from Set.image_subset_iff.mpr fun p hp => ?_)
    · rw [Set.InjOn.ncard_image, Set.ncard_prod]
      · simp [Set.ncard_univ, numC5Copies]
        exact Or.inl (by rw [← Set.ncard_coe_finset]; congr; ext; simp)
      · intro p hp q hq h_eq
        have := blowupC5Map_injective
          (show IsC5Copy G p.1 from hp.1) (show IsC5Copy G q.1 from hq.1) h_eq
        aesop
    · exact blowupC5Map_isC5Copy hp.1
  · convert Set.ncard_coe_finset _ |> le_of_eq
    aesop

/-!
## § 15. Combinatorial Bounds
-/

/-- `120 * C(M, 5) ≤ M ^ 5` for all `M : ℕ`. -/
lemma mul_choose_five_le (M : ℕ) : 120 * M.choose 5 ≤ M ^ 5 := by
  have h1 : M.choose 5 = M.descFactorial 5 / Nat.factorial 5 :=
    Nat.choose_eq_descFactorial_div_factorial M 5
  have h2 : Nat.factorial 5 = 120 := by norm_num
  rw [h1, h2]
  have h3 : 120 ∣ M.descFactorial 5 := by
    rw [← h2]; exact Nat.factorial_dvd_descFactorial M 5
  rw [Nat.mul_div_cancel' h3]
  exact Nat.descFactorial_le_pow M 5

/-- `C(M, 5) ≤ M⁵ / 120` over `ℝ`. -/
lemma choose_five_le_div (M : ℕ) :
    (M.choose 5 : ℝ) ≤ (M : ℝ) ^ 5 / 120 := by
  rw [le_div_iff₀ (by norm_num : (120 : ℝ) > 0)]
  have h := mul_choose_five_le M
  have : (120 : ℝ) * (M.choose 5 : ℝ) ≤ (M : ℝ) ^ 5 := by exact_mod_cast h
  linarith

/-!
## § 16. Main Theorem
-/

/-- Arithmetic identity: `(24/625 + 12/(625 · n⁵)) · (5n)⁵ / 120 = n⁵ + 1/2`. -/
lemma erdos_key_arithmetic (n : ℕ) (hn : 0 < n) :
    (24 / 625 + 12 / (625 * (n : ℝ) ^ 5)) * ((5 * (n : ℝ)) ^ 5 / 120) =
    (n : ℝ) ^ 5 + 1 / 2 := by
  have : (n : ℝ) ^ 5 ≠ 0 :=
    pow_ne_zero 5 (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))
  field_simp
  ring

/-- A natural number `c ≤ n⁵ + 1/2` (over `ℝ`) implies `c ≤ n⁵` (over `ℕ`). -/
lemma nat_le_of_real_le_add_half (c n : ℕ) (h : (c : ℝ) ≤ (n : ℝ) ^ 5 + 1 / 2) :
    c ≤ n ^ 5 := by
  have : (c : ℝ) < (n ^ 5 + 1 : ℕ) := by push_cast; linarith
  exact Nat.lt_add_one_iff.mp (Nat.cast_lt.mp this)

/-- **Erdős Pentagon Conjecture** (settled affirmatively by Grzesik, 2012).
  Statement in terms of `SimpleGraph.numC5Copies`. See `erdos_24` for
  a statement in terms of `SimpleGraph.numC5`. See Section §11 for a discussion on the
  differences between the two.

Every triangle-free graph on `5n` vertices contains at most `n⁵` copies of `C₅`.

The proof follows Grzesik's Theorem 2: assuming `c = numC5Copies G`, the balanced
blow-up `G.blowup N` is triangle-free with `≥ c · N⁵` copies of `C₅`. Choosing
`ε = 12/(625·n⁵)` and applying the Turán density bound to the blow-up gives
`c ≤ n⁵ + 1/2`, hence `c ≤ n⁵` since `c` is a natural number. -/
theorem numC5Copies_le_pow_five (n : ℕ) (G : SimpleGraph (Fin (5 * n)))
    (hG : G.CliqueFree 3) :
    numC5Copies G ≤ n ^ 5 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · show numC5Copies G ≤ 0
    simp only [Nat.le_zero]
    unfold numC5Copies
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _ ⟨f, _, _⟩
    exact Fin.elim0 (f 0)
  set c := numC5Copies G with hc_def
  set ε : ℝ := 12 / (625 * (n : ℝ) ^ 5) with hε_def
  have hε_pos : ε > 0 := by positivity
  obtain ⟨N₀, hN₀⟩ := flag_algebra_c5_turan_density ε hε_pos
  set N := max 1 N₀ with hN_def
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 N₀)
  have hcf := blowup_cliqueFree hG N
  have hcount := @blowup_numC5Copies_ge _ _ G N hN_pos
  have hcard : Fintype.card (Fin (5 * n) × Fin N) = 5 * n * N := by
    simp [Fintype.card_prod, Fintype.card_fin]
  have hcard_ge : Fintype.card (Fin (5 * n) × Fin N) ≥ N₀ := by
    rw [hcard]
    calc N₀ ≤ N := le_max_right 1 N₀
      _ = 1 * N := (one_mul N).symm
      _ ≤ (5 * n) * N := Nat.mul_le_mul_right N (by omega)
  have hfa := hN₀ (Fin (5 * n) × Fin N) hcard_ge (blowup G N) hcf
  have hN5 : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hε' : (0 : ℝ) ≤ 24 / 625 + ε := by linarith
  have h1 : (c : ℝ) * (N : ℝ) ^ 5 ≤
      (numC5Copies (blowup G N) : ℝ) := by exact_mod_cast hcount
  have h3 : ((Fintype.card (Fin (5 * n) × Fin N)).choose 5 : ℝ) ≤
      (Fintype.card (Fin (5 * n) × Fin N) : ℝ) ^ 5 / 120 :=
    choose_five_le_div _
  have hchain : (c : ℝ) * (N : ℝ) ^ 5 ≤
      (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) * (N : ℝ) ^ 5 := by
    calc (c : ℝ) * (N : ℝ) ^ 5
        ≤ (numC5Copies (blowup G N) : ℝ) := h1
      _ ≤ (24 / 625 + ε) *
            ((Fintype.card (Fin (5 * n) × Fin N)).choose 5 : ℝ) := hfa
      _ ≤ (24 / 625 + ε) *
            ((Fintype.card (Fin (5 * n) × Fin N) : ℝ) ^ 5 / 120) :=
          mul_le_mul_of_nonneg_left h3 hε'
      _ = (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) * (N : ℝ) ^ 5 := by
          rw [hcard]; push_cast; ring
  have hc_le : (c : ℝ) ≤ (24 / 625 + ε) * ((5 * (n : ℝ)) ^ 5 / 120) :=
    le_of_mul_le_mul_right hchain hN5
  rw [erdos_key_arithmetic n hn] at hc_le
  exact nat_le_of_real_le_add_half c n hc_le

/-!
## § 17. Equivalence of `numC5` and `numC5Copies` for Triangle-Free Graphs

In a triangle-free graph, each 5-vertex set supporting a 5-cycle admits a
unique cycle structure (up to the dihedral symmetry D₅), so the 10 labeled
5-cycles on that vertex set form a single orbit.  This gives
`|{f | IsLabeledC5 f}| = 10 * numC5Copies`, hence `numC5 = numC5Copies`.
-/

/-- The rotation `i ↦ i + 1` on `Fin 5`. -/
def rotate : Equiv.Perm (Fin 5) :=
  ⟨fun i => i + 1, fun i => i - 1,
   fun i => by simp,
   fun i => by simp⟩

/-- The reflection `i ↦ -i` (= `5 - i`) on `Fin 5`. -/
def reflect : Equiv.Perm (Fin 5) :=
  ⟨fun i => -i, fun i => -i,
   fun i => by simp,
   fun i => by simp⟩

/-- Rotating a labeled 5-cycle gives a labeled 5-cycle. -/
lemma IsLabeledC5_rotate {V : Type*} {G : SimpleGraph V}
    {f : Fin 5 → V} (hf : IsLabeledC5 G f) :
    IsLabeledC5 G (f ∘ rotate) := by
  constructor
  · exact hf.1.comp (Equiv.injective _)
  · intro i
    show G.Adj (f (i + 1)) (f (i + 1 + 1))
    exact hf.2 (i + 1)

/-- Reflecting a labeled 5-cycle gives a labeled 5-cycle. -/
lemma IsLabeledC5_reflect {V : Type*} {G : SimpleGraph V}
    {f : Fin 5 → V} (hf : IsLabeledC5 G f) :
    IsLabeledC5 G (f ∘ reflect) := by
  constructor
  · exact hf.1.comp (Equiv.injective _)
  · intro i
    show G.Adj (f (-i)) (f (-(i + 1)))
    have : G.Adj (f (-(i+1))) (f (-(i+1) + 1)) := hf.2 (-(i+1))
    have h2 : -(i + 1) + 1 = -i := by fin_cases i <;> decide
    rw [h2] at this
    exact this.symm

set_option maxHeartbeats 6400000 in
/-- In a triangle-free graph, non-consecutive vertices of a labeled 5-cycle are
non-adjacent. Equivalently, the induced subgraph on the 5 vertices is exactly C₅
(no chords), because any chord in a 5-cycle creates a triangle. -/
lemma triangleFree_C5_no_chords {V : Type*} {G : SimpleGraph V}
    (hG : G.CliqueFree 3)
    {f : Fin 5 → V} (hf : IsLabeledC5 G f)
    (i j : Fin 5) (hij : j ≠ i + 1) (hji : i ≠ j + 1) (hne : i ≠ j) :
    ¬G.Adj (f i) (f j) := by
  intro hadj
  have h := hf.2
  have h01 : G.Adj (f 0) (f 1) := h 0
  have h12 : G.Adj (f 1) (f 2) := h 1
  have h23 : G.Adj (f 2) (f 3) := h 2
  have h34 : G.Adj (f 3) (f 4) := h 3
  have h40 : G.Adj (f 4) (f 0) := by have := h 4; simp at this; exact this
  have tri : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c →
      G.Adj (f a) (f b) → G.Adj (f a) (f c) → G.Adj (f b) (f c) → False := by
    intro a b c hab hac hbc e1 e2 e3
    apply hG {f a, f b, f c}
    constructor
    · intro x hx y hy hxy
      simp at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first | exact absurd rfl hxy | assumption | exact SimpleGraph.Adj.symm ‹_›
    · simp [hf.1.ne hab, hf.1.ne hac, hf.1.ne hbc]
  fin_cases i <;> fin_cases j <;> simp_all (config := { decide := true })
  · exact tri 0 2 1 (by decide) (by decide) (by decide) hadj h01 h12.symm
  · exact tri 0 3 4 (by decide) (by decide) (by decide) hadj h40.symm h34
  · exact tri 1 3 2 (by decide) (by decide) (by decide) hadj h12 h23.symm
  · exact tri 1 4 0 (by decide) (by decide) (by decide) hadj h01.symm h40
  · exact tri 2 0 1 (by decide) (by decide) (by decide) hadj h12.symm h01
  · exact tri 2 4 3 (by decide) (by decide) (by decide) hadj h23 h34.symm
  · exact tri 3 0 4 (by decide) (by decide) (by decide) hadj h34 h40.symm
  · exact tri 3 1 2 (by decide) (by decide) (by decide) hadj h23.symm h12
  · exact tri 4 1 0 (by decide) (by decide) (by decide) hadj h40 h01.symm
  · exact tri 4 2 3 (by decide) (by decide) (by decide) hadj h34.symm h23

/-
In a triangle-free graph, the number of labeled 5-cycles on a given vertex set
is exactly 10 (the order of the dihedral group D₅).

The proof uses `triangleFree_C5_no_chords` to show that the only permutations
preserving the cycle structure are the 10 dihedral symmetries (5 rotations ×
2 orientations).
-/
lemma labeledC5_fiber_card {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : G.CliqueFree 3)
    {S : Finset V} (hS : IsC5Copy G S) :
    ((Finset.univ : Finset (Fin 5 → V)).filter
      (fun f => IsLabeledC5 G f ∧ Finset.image f Finset.univ = S)).card = 10 := by
        revert hS S;
        intro S hS
        obtain ⟨f₀, hf₀⟩ := hS
        have h_adj : ∀ i j : Fin 5, G.Adj (f₀ i) (f₀ j) ↔ (j = i + 1 ∨ i = j + 1) := by
          intro i j;
          constructor;
          · intro hij
            by_contra h_contra;
            exact triangleFree_C5_no_chords hG hf₀.1 i j ( by tauto ) ( by tauto ) ( by aesop ) hij;
          · rintro ( rfl | rfl ) <;> simp_all +decide [ IsLabeledC5 ];
            simpa [ SimpleGraph.adj_comm ] using hf₀.1.2 j;
        -- We need to show that the set of labeled 5-cycles on $S$ is in bijection with the set of dihedral permutations of $\{0, 1, 2, 3, 4\}$.
        have h_bij : {f : Fin 5 → V | IsLabeledC5 G f ∧ Finset.image f Finset.univ = S} = Finset.image (fun σ : Equiv.Perm (Fin 5) => fun i => f₀ (σ i)) (Finset.filter (fun σ : Equiv.Perm (Fin 5) => ∀ i, σ (i + 1) = σ i + 1 ∨ σ i = σ (i + 1) + 1) (Finset.univ : Finset (Equiv.Perm (Fin 5)))) := by
          ext f; simp;
          constructor;
          · intro hf
            obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin 5), ∀ i, f i = f₀ (σ i) := by
              have h_bij : ∀ i, ∃ j, f i = f₀ j := by
                intro i
                have h_mem : f i ∈ S := by
                  exact hf.2 ▸ Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
                grind +qlia;
              choose σ hσ using h_bij;
              have hσ_inj : Function.Injective σ := by
                intro i j hij; have := hf.1.1; have := hf₀.1.1; aesop;
              exact ⟨ Equiv.ofBijective σ ⟨ hσ_inj, Finite.injective_iff_surjective.mp hσ_inj ⟩, hσ ⟩;
            use σ;
            simp_all +decide [ funext_iff, IsLabeledC5 ];
          · rintro ⟨ σ, hσ, rfl ⟩ ; simp_all +decide [ IsLabeledC5 ] ;
            simp_all +decide [ Finset.ext_iff, Function.Injective ];
            exact ⟨ fun i j hij => σ.injective ( hf₀.1 hij ), fun a => by rw [ ← hf₀.2 a ] ; exact ⟨ fun ⟨ i, hi ⟩ => ⟨ σ i, hi ⟩, fun ⟨ i, hi ⟩ => ⟨ σ.symm i, by simpa using hi ⟩ ⟩ ⟩;
        rw [ Set.ext_iff ] at h_bij;
        convert Finset.card_image_of_injective _ ( show Function.Injective ( fun σ : Equiv.Perm ( Fin 5 ) => fun i => f₀ ( σ i ) ) from ?_ ) using 1;
        any_goals exact Finset.filter ( fun σ : Equiv.Perm ( Fin 5 ) => ∀ i : Fin 5, σ ( i + 1 ) = σ i + 1 ∨ σ i = σ ( i + 1 ) + 1 ) Finset.univ;
        · exact congr_arg Finset.card ( Finset.ext fun x => by simpa using h_bij x );
        · set_option maxRecDepth 8192 in set_option maxHeartbeats 6400000 in decide;
        · intro σ τ hστ; have := hf₀.1.1; simp_all +decide [ funext_iff, Fin.forall_fin_succ ] ;
          exact Equiv.Perm.ext fun x => this <| by fin_cases x <;> tauto;

/-
In a triangle-free graph, `numC5 = numC5Copies`.

Each 5-element vertex set supporting a cycle gives rise to exactly 10
labeled 5-cycles (one orbit under D₅), so
`|{f | IsLabeledC5 f}| = 10 * numC5Copies` and dividing by 10 recovers
`numC5Copies`.
-/
theorem numC5_eq_numC5Copies_of_triangleFree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    numC5 G = numC5Copies G := by
      have := @labeledC5_fiber_card;
      rw [ eq_comm, numC5, numC5Copies ];
      rw [ Nat.div_eq_of_eq_mul_left ];
      decide +revert;
      rw [ ← Finset.sum_const_nat ];
      nontriviality;
      convert Finset.card_biUnion _;
      rotate_left;
      infer_instance;
      rotate_left;
      intro S hS;
      convert this hG ( Finset.mem_filter.mp hS |>.2 );
      · ext f; simp [IsC5Copy];
        grind +qlia;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun f hf₁ hf₂ => hxy <| by aesop;

/-- **Erdős Pentagon Conjecture** (settled affirmatively by Grzesik, 2012).

Every triangle-free graph on `5n` vertices contains at most `n⁵` copies of `C₅`,
where copies are counted as subgraphs isomorphic to the cycle graph `C₅`
(see `SimpleGraph.numC5` and Section §11). -/
theorem erdos_24 (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (hG : G.CliqueFree 3) :
    numC5 G ≤ n ^ 5 := by
  rw [numC5_eq_numC5Copies_of_triangleFree G hG]
  exact numC5Copies_le_pow_five n G hG

#print axioms erdos_24
-- 'Erdos24.erdos_24' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos24
