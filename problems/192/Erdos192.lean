import Mathlib

namespace Erdos192

/-
# Problem Description

Erdős Problem 192. Let `A = {a₁, a₂, …} ⊂ ℝ^d` be an infinite sequence such that
`aᵢ₊₁ - aᵢ` is a positive unit vector, i.e. of the form `(0,0,…,1,0,…,0)`. For which `d`
must `A` contain a three-term arithmetic progression? `erdos_192` answers this: exactly
for `d ≤ 3`.

`erdos_192` is proved here without `native_decide`: the finite Keränen obligations are
kernel checked using prefix-count, streaming and bitset certificates, so the proof depends
on Lean's standard foundations alone rather than on `Lean.ofReduceBool` and
`Lean.trustCompiler`.

`erdos_192` is also restated in the geometric form the problem is posed in, over positive
unit walks in `ℝ^d`. The word form this repository previously used — for which `d` is
every infinite string over `d` letters forced to contain an abelian square, equivalently a
Parikh three-term progression — is retained as `erdos_problem_192_classification`, and
`geometric_classification_iff_words` connects the two. erdosproblems.com describes that
equivalence explicitly: `A` is read as a string over `d` letters recording which step is
taken at each point.

The formalisation is by plby (github.com/plby/lean-proofs),
`src/latest/ErdosProblems/Erdos192.lean`, adapting the construction and parts of the
infrastructure from Lorenzo Luccioli's Aristotle formalisation
(github.com/LorenzoLuccioli/KE92ErdosProblems).

Flattened single-file vendoring of the 22-module import closure, in dependency order, with
project-internal imports removed so that `Mathlib` is the only import, each module wrapped
in its own `section` with any end-of-file scopes closed explicitly. `Erdos192` is the only
namespace used upstream, and it is stripped from the modules that carry it since the whole
file is wrapped in it once, and `erdos_192` is moved to the end so that it is the final
declaration. Declarations not reachable from `erdos_192` are dropped, so everything here
is inside its trust base; attribute-tagged lemmas and instances are kept regardless, since
they can be used implicitly. No mathematical content is changed.
-/

/-! ### Upstream module `ErdosProblems/Erdos192/Core.lean` -/

section
/-!
# KE92 shared definitions and basic lemmas

Definitions and foundational lemmas for the Keränen 1992 formalization.
Separated from `KE92.lean` so that bounded verification files can
-/



/-! ### Finite-word abelian-square-free definitions -/

def infBlock {α : Type*} (f : ℕ → α) (start len : ℕ) : List α :=
  (List.range len).map (fun j => f (start + j))

def InfAbelianSquareFree {α : Type*} [DecidableEq α] (f : ℕ → α) : Prop :=
  ∀ i l, l > 0 → ¬ (infBlock f i l).Perm (infBlock f (i + l) l)

def FinAbelianSquareFree {n : ℕ} (w : List (Fin n)) : Prop :=
  ∀ i l : ℕ, l > 0 → i + 2 * l ≤ w.length →
    ¬ (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l)


def hasAbelianSquareAt (word : List Nat) (i l : Nat) : Bool :=
  if l == 0 then false
  else if i + 2 * l > word.length then false
  else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l)


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
    refine' fun h => h ⟨ i, i + l, i + 2 * l, _, _, _ ⟩ <;> simp_all +decide [ two_mul, add_assoc ];
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
  fin_cases c <;> decide

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


theorem singleton_finASF (c : Fin 4) : FinAbelianSquareFree [c] := by
  intro i l hl hlen; simp at hlen; omega

end
section
def cumParikhCount (a : Fin 4) (k : Nat) (c : Fin 4) : Nat :=
  ((keranenG a).take k).count c

def sliceParikhCount (a : Fin 4) (lo hi : Nat) (c : Fin 4) : Int :=
  (cumParikhCount a hi c : Int) - (cumParikhCount a lo c : Int)

def boundaryDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let t := (2 * s + 85 * 1000 - r) % 85
  sliceParikhCount wb s 85 c + sliceParikhCount we 0 t c
  - sliceParikhCount wa r 85 c - sliceParikhCount wb 0 s c

def adjMTtimesDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d : Fin 4 → Int := boundaryDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

def parikhSolutionVec (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  adjMTtimesDelta wa wb we r s c / 43435

/-- Helper: check if solution exists (divisibility) -/
def hasParikhSolution (wa wb we : Fin 4) (r s : Nat) : Bool :=
  adjMTtimesDelta wa wb we r s 0 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 1 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 2 % 43435 = 0 &&
  adjMTtimesDelta wa wb we r s 3 % 43435 = 0

def vGivesSomeAS (wa wb we : Fin 4) (v : Fin 4 → Int) : Bool :=
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) - (if c = we then 1 else 0) == 0) ||
  ((List.finRange 4).all fun c => v c - (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => v c + (if c = wb then (1:Int) else 0) == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) - (if c = we then 1 else 0) + v c == 0) ||
  ((List.finRange 4).all fun c => (if c = wa then (1:Int) else 0) + (if c = wb then 1 else 0) + v c - (if c = we then 1 else 0) == 0)

end


/-! ### Upstream module `ErdosProblems/Erdos192/PrefixData.lean` -/

section
def prefixData : Array (Array (Array Nat)) :=
  #[
    #[
      #[0, 0, 0, 0],
      #[1, 0, 0, 0],
      #[1, 1, 0, 0],
      #[1, 1, 1, 0],
      #[2, 1, 1, 0],
      #[2, 1, 2, 0],
      #[2, 1, 2, 1],
      #[2, 1, 3, 1],
      #[2, 2, 3, 1],
      #[2, 2, 4, 1],
      #[2, 2, 4, 2],
      #[2, 2, 5, 2],
      #[3, 2, 5, 2],
      #[3, 2, 5, 3],
      #[3, 2, 6, 3],
      #[3, 2, 6, 4],
      #[3, 3, 6, 4],
      #[3, 3, 6, 5],
      #[4, 3, 6, 5],
      #[4, 4, 6, 5],
      #[5, 4, 6, 5],
      #[5, 4, 7, 5],
      #[6, 4, 7, 5],
      #[6, 5, 7, 5],
      #[7, 5, 7, 5],
      #[7, 5, 7, 6],
      #[7, 6, 7, 6],
      #[8, 6, 7, 6],
      #[8, 7, 7, 6],
      #[8, 7, 8, 6],
      #[8, 8, 8, 6],
      #[8, 8, 8, 7],
      #[8, 9, 8, 7],
      #[8, 9, 9, 7],
      #[8, 10, 9, 7],
      #[9, 10, 9, 7],
      #[9, 10, 10, 7],
      #[9, 11, 10, 7],
      #[9, 11, 11, 7],
      #[9, 11, 11, 8],
      #[9, 11, 12, 8],
      #[10, 11, 12, 8],
      #[10, 11, 13, 8],
      #[10, 12, 13, 8],
      #[11, 12, 13, 8],
      #[11, 13, 13, 8],
      #[11, 13, 13, 9],
      #[12, 13, 13, 9],
      #[12, 14, 13, 9],
      #[13, 14, 13, 9],
      #[13, 14, 14, 9],
      #[14, 14, 14, 9],
      #[14, 14, 14, 10],
      #[14, 14, 15, 10],
      #[14, 15, 15, 10],
      #[14, 15, 16, 10],
      #[14, 15, 16, 11],
      #[14, 15, 17, 11],
      #[15, 15, 17, 11],
      #[15, 15, 18, 11],
      #[15, 15, 18, 12],
      #[15, 16, 18, 12],
      #[15, 16, 19, 12],
      #[15, 17, 19, 12],
      #[16, 17, 19, 12],
      #[16, 17, 20, 12],
      #[16, 18, 20, 12],
      #[16, 18, 21, 12],
      #[16, 18, 21, 13],
      #[16, 18, 22, 13],
      #[17, 18, 22, 13],
      #[17, 18, 23, 13],
      #[17, 18, 23, 14],
      #[17, 18, 24, 14],
      #[17, 19, 24, 14],
      #[17, 19, 24, 15],
      #[17, 19, 25, 15],
      #[17, 19, 25, 16],
      #[18, 19, 25, 16],
      #[18, 19, 25, 17],
      #[18, 20, 25, 17],
      #[18, 20, 25, 18],
      #[18, 20, 26, 18],
      #[18, 21, 26, 18],
      #[18, 21, 27, 18],
      #[19, 21, 27, 18]
    ],
    #[
      #[0, 0, 0, 0],
      #[0, 1, 0, 0],
      #[0, 1, 1, 0],
      #[0, 1, 1, 1],
      #[0, 2, 1, 1],
      #[0, 2, 1, 2],
      #[1, 2, 1, 2],
      #[1, 2, 1, 3],
      #[1, 2, 2, 3],
      #[1, 2, 2, 4],
      #[2, 2, 2, 4],
      #[2, 2, 2, 5],
      #[2, 3, 2, 5],
      #[3, 3, 2, 5],
      #[3, 3, 2, 6],
      #[4, 3, 2, 6],
      #[4, 3, 3, 6],
      #[5, 3, 3, 6],
      #[5, 4, 3, 6],
      #[5, 4, 4, 6],
      #[5, 5, 4, 6],
      #[5, 5, 4, 7],
      #[5, 6, 4, 7],
      #[5, 6, 5, 7],
      #[5, 7, 5, 7],
      #[6, 7, 5, 7],
      #[6, 7, 6, 7],
      #[6, 8, 6, 7],
      #[6, 8, 7, 7],
      #[6, 8, 7, 8],
      #[6, 8, 8, 8],
      #[7, 8, 8, 8],
      #[7, 8, 9, 8],
      #[7, 8, 9, 9],
      #[7, 8, 10, 9],
      #[7, 9, 10, 9],
      #[7, 9, 10, 10],
      #[7, 9, 11, 10],
      #[7, 9, 11, 11],
      #[8, 9, 11, 11],
      #[8, 9, 11, 12],
      #[8, 10, 11, 12],
      #[8, 10, 11, 13],
      #[8, 10, 12, 13],
      #[8, 11, 12, 13],
      #[8, 11, 13, 13],
      #[9, 11, 13, 13],
      #[9, 12, 13, 13],
      #[9, 12, 14, 13],
      #[9, 13, 14, 13],
      #[9, 13, 14, 14],
      #[9, 14, 14, 14],
      #[10, 14, 14, 14],
      #[10, 14, 14, 15],
      #[10, 14, 15, 15],
      #[10, 14, 15, 16],
      #[11, 14, 15, 16],
      #[11, 14, 15, 17],
      #[11, 15, 15, 17],
      #[11, 15, 15, 18],
      #[12, 15, 15, 18],
      #[12, 15, 16, 18],
      #[12, 15, 16, 19],
      #[12, 15, 17, 19],
      #[12, 16, 17, 19],
      #[12, 16, 17, 20],
      #[12, 16, 18, 20],
      #[12, 16, 18, 21],
      #[13, 16, 18, 21],
      #[13, 16, 18, 22],
      #[13, 17, 18, 22],
      #[13, 17, 18, 23],
      #[14, 17, 18, 23],
      #[14, 17, 18, 24],
      #[14, 17, 19, 24],
      #[15, 17, 19, 24],
      #[15, 17, 19, 25],
      #[16, 17, 19, 25],
      #[16, 18, 19, 25],
      #[17, 18, 19, 25],
      #[17, 18, 20, 25],
      #[18, 18, 20, 25],
      #[18, 18, 20, 26],
      #[18, 18, 21, 26],
      #[18, 18, 21, 27],
      #[18, 19, 21, 27]
    ],
    #[
      #[0, 0, 0, 0],
      #[0, 0, 1, 0],
      #[0, 0, 1, 1],
      #[1, 0, 1, 1],
      #[1, 0, 2, 1],
      #[2, 0, 2, 1],
      #[2, 1, 2, 1],
      #[3, 1, 2, 1],
      #[3, 1, 2, 2],
      #[4, 1, 2, 2],
      #[4, 2, 2, 2],
      #[5, 2, 2, 2],
      #[5, 2, 3, 2],
      #[5, 3, 3, 2],
      #[6, 3, 3, 2],
      #[6, 4, 3, 2],
      #[6, 4, 3, 3],
      #[6, 5, 3, 3],
      #[6, 5, 4, 3],
      #[6, 5, 4, 4],
      #[6, 5, 5, 4],
      #[7, 5, 5, 4],
      #[7, 5, 6, 4],
      #[7, 5, 6, 5],
      #[7, 5, 7, 5],
      #[7, 6, 7, 5],
      #[7, 6, 7, 6],
      #[7, 6, 8, 6],
      #[7, 6, 8, 7],
      #[8, 6, 8, 7],
      #[8, 6, 8, 8],
      #[8, 7, 8, 8],
      #[8, 7, 8, 9],
      #[9, 7, 8, 9],
      #[9, 7, 8, 10],
      #[9, 7, 9, 10],
      #[10, 7, 9, 10],
      #[10, 7, 9, 11],
      #[11, 7, 9, 11],
      #[11, 8, 9, 11],
      #[12, 8, 9, 11],
      #[12, 8, 10, 11],
      #[13, 8, 10, 11],
      #[13, 8, 10, 12],
      #[13, 8, 11, 12],
      #[13, 8, 11, 13],
      #[13, 9, 11, 13],
      #[13, 9, 12, 13],
      #[13, 9, 12, 14],
      #[13, 9, 13, 14],
      #[14, 9, 13, 14],
      #[14, 9, 14, 14],
      #[14, 10, 14, 14],
      #[15, 10, 14, 14],
      #[15, 10, 14, 15],
      #[16, 10, 14, 15],
      #[16, 11, 14, 15],
      #[17, 11, 14, 15],
      #[17, 11, 15, 15],
      #[18, 11, 15, 15],
      #[18, 12, 15, 15],
      #[18, 12, 15, 16],
      #[19, 12, 15, 16],
      #[19, 12, 15, 17],
      #[19, 12, 16, 17],
      #[20, 12, 16, 17],
      #[20, 12, 16, 18],
      #[21, 12, 16, 18],
      #[21, 13, 16, 18],
      #[22, 13, 16, 18],
      #[22, 13, 17, 18],
      #[23, 13, 17, 18],
      #[23, 14, 17, 18],
      #[24, 14, 17, 18],
      #[24, 14, 17, 19],
      #[24, 15, 17, 19],
      #[25, 15, 17, 19],
      #[25, 16, 17, 19],
      #[25, 16, 18, 19],
      #[25, 17, 18, 19],
      #[25, 17, 18, 20],
      #[25, 18, 18, 20],
      #[26, 18, 18, 20],
      #[26, 18, 18, 21],
      #[27, 18, 18, 21],
      #[27, 18, 19, 21]
    ],
    #[
      #[0, 0, 0, 0],
      #[0, 0, 0, 1],
      #[1, 0, 0, 1],
      #[1, 1, 0, 1],
      #[1, 1, 0, 2],
      #[1, 2, 0, 2],
      #[1, 2, 1, 2],
      #[1, 3, 1, 2],
      #[2, 3, 1, 2],
      #[2, 4, 1, 2],
      #[2, 4, 2, 2],
      #[2, 5, 2, 2],
      #[2, 5, 2, 3],
      #[2, 5, 3, 3],
      #[2, 6, 3, 3],
      #[2, 6, 4, 3],
      #[3, 6, 4, 3],
      #[3, 6, 5, 3],
      #[3, 6, 5, 4],
      #[4, 6, 5, 4],
      #[4, 6, 5, 5],
      #[4, 7, 5, 5],
      #[4, 7, 5, 6],
      #[5, 7, 5, 6],
      #[5, 7, 5, 7],
      #[5, 7, 6, 7],
      #[6, 7, 6, 7],
      #[6, 7, 6, 8],
      #[7, 7, 6, 8],
      #[7, 8, 6, 8],
      #[8, 8, 6, 8],
      #[8, 8, 7, 8],
      #[9, 8, 7, 8],
      #[9, 9, 7, 8],
      #[10, 9, 7, 8],
      #[10, 9, 7, 9],
      #[10, 10, 7, 9],
      #[11, 10, 7, 9],
      #[11, 11, 7, 9],
      #[11, 11, 8, 9],
      #[11, 12, 8, 9],
      #[11, 12, 8, 10],
      #[11, 13, 8, 10],
      #[12, 13, 8, 10],
      #[12, 13, 8, 11],
      #[13, 13, 8, 11],
      #[13, 13, 9, 11],
      #[13, 13, 9, 12],
      #[14, 13, 9, 12],
      #[14, 13, 9, 13],
      #[14, 14, 9, 13],
      #[14, 14, 9, 14],
      #[14, 14, 10, 14],
      #[14, 15, 10, 14],
      #[15, 15, 10, 14],
      #[15, 16, 10, 14],
      #[15, 16, 11, 14],
      #[15, 17, 11, 14],
      #[15, 17, 11, 15],
      #[15, 18, 11, 15],
      #[15, 18, 12, 15],
      #[16, 18, 12, 15],
      #[16, 19, 12, 15],
      #[17, 19, 12, 15],
      #[17, 19, 12, 16],
      #[17, 20, 12, 16],
      #[18, 20, 12, 16],
      #[18, 21, 12, 16],
      #[18, 21, 13, 16],
      #[18, 22, 13, 16],
      #[18, 22, 13, 17],
      #[18, 23, 13, 17],
      #[18, 23, 14, 17],
      #[18, 24, 14, 17],
      #[19, 24, 14, 17],
      #[19, 24, 15, 17],
      #[19, 25, 15, 17],
      #[19, 25, 16, 17],
      #[19, 25, 16, 18],
      #[19, 25, 17, 18],
      #[20, 25, 17, 18],
      #[20, 25, 18, 18],
      #[20, 26, 18, 18],
      #[21, 26, 18, 18],
      #[21, 27, 18, 18],
      #[21, 27, 18, 19]
    ]
  ]

def fastPrefix (a : Fin 4) (k : Nat) (c : Fin 4) : Nat :=
  ((prefixData[a.val]!).getD k #[]).getD c.val 0

theorem prefixData_correct : ∀ a : Fin 4, ∀ k : Fin 86, ∀ c : Fin 4,
    fastPrefix a k.val c = cumParikhCount a k.val c := by decide +kernel

end


/-! ### Upstream module `ErdosProblems/Erdos192/PackedData.lean` -/

section
def packedData : Array (Array Nat) :=
  #[
    #[0, 1, 257, 65793, 65794, 131330, 16908546, 16974082, 16974338, 17039874, 33817090, 33882626, 33882627, 50659843, 50725379, 67502595, 67502851, 84280067, 84280068, 84280324, 84280325, 84345861, 84345862, 84346118, 84346119, 101123335, 101123591, 101123592, 101123848, 101189384, 101189640, 117966856, 117967112, 118032648, 118032904, 118032905, 118098441, 118098697, 118164233, 134941449, 135006985, 135006986, 135072522, 135072778, 135072779, 135073035, 151850251, 151850252, 151850508, 151850509, 151916045, 151916046, 168693262, 168758798, 168759054, 168824590, 185601806, 185667342, 185667343, 185732879, 202510095, 202510351, 202575887, 202576143, 202576144, 202641680, 202641936, 202707472, 219484688, 219550224, 219550225, 219615761, 236392977, 236458513, 236458769, 253235985, 253301521, 270078737, 270078738, 286855954, 286856210, 303633426, 303698962, 303699218, 303764754, 303764755],
    #[0, 256, 65792, 16843008, 16843264, 33620480, 33620481, 50397697, 50463233, 67240449, 67240450, 84017666, 84017922, 84017923, 100795139, 100795140, 100860676, 100860677, 100860933, 100926469, 100926725, 117703941, 117704197, 117769733, 117769989, 117769990, 117835526, 117835782, 117901318, 134678534, 134744070, 134744071, 134809607, 151586823, 151652359, 151652615, 168429831, 168495367, 185272583, 185272584, 202049800, 202050056, 218827272, 218892808, 218893064, 218958600, 218958601, 218958857, 219024393, 219024649, 235801865, 235802121, 235802122, 252579338, 252644874, 269422090, 269422091, 286199307, 286199563, 302976779, 302976780, 303042316, 319819532, 319885068, 319885324, 336662540, 336728076, 353505292, 353505293, 370282509, 370282765, 387059981, 387059982, 403837198, 403902734, 403902735, 420679951, 420679952, 420680208, 420680209, 420745745, 420745746, 437522962, 437588498, 454365714, 454365970],
    #[0, 65536, 16842752, 16842753, 16908289, 16908290, 16908546, 16908547, 33685763, 33685764, 33686020, 33686021, 33751557, 33751813, 33751814, 33752070, 50529286, 50529542, 50595078, 67372294, 67437830, 67437831, 67503367, 84280583, 84346119, 84346375, 101123591, 101189127, 117966343, 117966344, 134743560, 134743816, 151521032, 151521033, 168298249, 168363785, 168363786, 185141002, 185141003, 185141259, 185141260, 185206796, 185206797, 201984013, 202049549, 218826765, 218827021, 218892557, 235669773, 235735309, 235735310, 235800846, 235801102, 235801103, 252578319, 252578320, 252578576, 252578577, 252644113, 252644114, 252644370, 269421586, 269421587, 286198803, 286264339, 286264340, 303041556, 303041557, 303041813, 303041814, 303107350, 303107351, 303107607, 303107608, 319884824, 319885080, 319885081, 319885337, 319950873, 319951129, 336728345, 336728601, 336728602, 353505818, 353505819, 353571355],
    #[0, 16777216, 16777217, 16777473, 33554689, 33554945, 33620481, 33620737, 33620738, 33620994, 33686530, 33686786, 50464002, 50529538, 50529794, 50595330, 50595331, 50660867, 67438083, 67438084, 84215300, 84215556, 100992772, 100992773, 117769989, 117835525, 117835526, 134612742, 134612743, 134612999, 134613000, 134678536, 134678537, 134678793, 134678794, 151456010, 151456266, 151456267, 151456523, 151522059, 151522315, 168299531, 168299787, 168299788, 185077004, 185077005, 185142541, 201919757, 201919758, 218696974, 218697230, 235474446, 235539982, 235540238, 235540239, 235540495, 235606031, 235606287, 252383503, 252383759, 252449295, 252449296, 252449552, 252449553, 269226769, 269227025, 269227026, 269227282, 269292818, 269293074, 286070290, 286070546, 286136082, 286136338, 286136339, 286201875, 286202131, 286267667, 303044883, 303110419, 303110420, 303175956, 303176212, 303176213, 303176469, 319953685]
  ]

def packedPrefix (a : Fin 4) (n : Nat) : Nat := (packedData[a.val]!).getD n 0

theorem packedPrefix_correct : ∀ a : Fin 4, ∀ n : Fin 86,
  packedPrefix a n.val = fastPrefix a n.val 0 + 256 * fastPrefix a n.val 1 +
    65536 * fastPrefix a n.val 2 + 16777216 * fastPrefix a n.val 3 := by decide +kernel

end


/-! ### Upstream module `ErdosProblems/Erdos192/ListAPCheck.lean` -/

section
/-- Scan possible midpoints once, moving the endpoint twice per iteration. -/
def halfChecks (x : Nat) : List Nat → List Nat → Bool
  | m :: ms, e :: es => (x + e != 2 * m) && halfChecks x ms (es.drop 1)
  | _, _ => true

def allChecks : List Nat → Bool
  | [] => true
  | x :: xs => halfChecks x xs (xs.drop 1) && allChecks xs

theorem halfChecks_sound (x : Nat) (ms es : List Nat) (h : halfChecks x ms es = true)
    (k : Nat) (hk : k < ms.length) (he : 2 * k < es.length) :
    x + es[2 * k] ≠ 2 * ms[k] := by
  induction ms generalizing es k with
  | nil => simp at hk
  | cons m ms ih =>
    cases es with
    | nil => simp at he
    | cons e es =>
      simp only [halfChecks, Bool.and_eq_true, bne_iff_ne] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
        have hk' : k < ms.length := by simpa using hk
        have he' : 2 * k < (es.drop 1).length := by simp at he ⊢; omega
        have hs := ih (es.drop 1) h.2 k hk' he'
        simp only [show 2 * (k + 1) = (1 + 2 * k) + 1 by omega,
          List.getElem_cons_succ]
        simpa only [List.getElem_drop] using hs

theorem allChecks_sound (p : List Nat) (h : allChecks p = true) (i l : Nat)
    (hl : 0 < l) (hend : i + 2 * l < p.length) :
    p[i] + p[i + 2 * l] ≠ 2 * p[i + l] := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  induction p generalizing i with
  | nil => simp at hend
  | cons x xs ih =>
    simp only [allChecks, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have hm : k < xs.length := by simp at hend; omega
      have he : 2 * k < (xs.drop 1).length := by simp at hend ⊢; omega
      have hs := halfChecks_sound x xs (xs.drop 1) h.1 k hm he
      simp only [Nat.zero_add, List.getElem_cons_zero,
        show 2 * (k + 1) = (1 + 2 * k) + 1 by omega, List.getElem_cons_succ]
      simpa only [List.getElem_drop] using hs
    | succ i =>
      have he : i + 2 * (k + 1) < xs.length := by simp at hend; omega
      simpa only [Nat.succ_add, List.getElem_cons_succ] using ih h.2 i he

end


/-! ### Upstream module `ErdosProblems/Erdos192/ShortCheck.lean` -/

section
def pairPrefix (a b : Fin 4) (n : Nat) (c : Fin 4) : Nat :=
  if n ≤ 85 then fastPrefix a n c else fastPrefix a 85 c + fastPrefix b (n - 85) c

def packedPairPrefix (a b : Fin 4) (n : Nat) : Nat :=
  if n ≤ 85 then packedPrefix a n else packedPrefix a 85 + packedPrefix b (n - 85)

def pairPrefixList (a b : Fin 4) : List Nat :=
  (List.range 171).map (packedPairPrefix a b)

def pairsCheck : Bool :=
  (List.finRange 4).all fun a =>
  (List.finRange 4).all fun b => a == b || allChecks (pairPrefixList a b)

theorem pairsCheck_true : pairsCheck = true := by decide +kernel

theorem pairPrefix_eq (a b : Fin 4) (n : Nat) (hn : n ≤ 170) (c : Fin 4) :
    pairPrefix a b n c = ((applyKeranenG [a, b]).take n).count c := by
  simp only [applyKeranenG, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold pairPrefix
  split_ifs with h
  · rw [prefixData_correct a ⟨n, by omega⟩ c]
    rw [List.take_append_of_le_length (by simpa [keranenG_length] using h)]
    rfl
  · rw [prefixData_correct a ⟨85, by decide⟩ c,
      prefixData_correct b ⟨n - 85, by omega⟩ c]
    simp only [cumParikhCount, List.take_append, keranenG_length, List.count_append]
    rw [List.take_of_length_le (l := keranenG a) (by rw [keranenG_length]),
      List.take_of_length_le (l := keranenG a) (by rw [keranenG_length]; omega)]

theorem count_prefix_square {w : List (Fin 4)} (i l : Nat)
    (h : (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l)) (c : Fin 4) :
    (w.take i).count c + (w.take (i + 2 * l)).count c =
      2 * (w.take (i + l)).count c := by
  have hc := h.count_eq c
  rw [show i + 2 * l = (i + l) + l by omega, List.take_add, List.count_append,
    List.take_add, List.count_append]
  omega

theorem packedPairPrefix_eq (a b : Fin 4) (n : Nat) (hn : n ≤ 170) :
    packedPairPrefix a b n = pairPrefix a b n 0 + 256 * pairPrefix a b n 1 +
      65536 * pairPrefix a b n 2 + 16777216 * pairPrefix a b n 3 := by
  unfold packedPairPrefix pairPrefix
  split_ifs with h
  · exact packedPrefix_correct a ⟨n, by omega⟩
  · rw [packedPrefix_correct a ⟨85, by decide⟩, packedPrefix_correct b ⟨n - 85, by omega⟩]
    ring

theorem keranen_pair_asf (a b : Fin 4) (hab : a ≠ b) :
    FinAbelianSquareFree (applyKeranenG [a, b]) := by
  have h := pairsCheck_true
  simp only [pairsCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq] at h
  have h := (h a b).resolve_left hab
  intro i l hl hlen hp
  have hlen' : i + 2 * l ≤ 170 := by simpa [applyKeranenG_length] using hlen
  have hend : i + 2 * l < (pairPrefixList a b).length := by
    simp only [pairPrefixList, List.length_map, List.length_range]; omega
  have hs := allChecks_sound (pairPrefixList a b) h i l hl hend
  simp only [pairPrefixList, List.getElem_map, List.getElem_range] at hs
  rw [packedPairPrefix_eq a b i (by omega),
    packedPairPrefix_eq a b (i + 2 * l) (by omega),
    packedPairPrefix_eq a b (i + l) (by omega)] at hs
  have hc (c : Fin 4) : pairPrefix a b i c + pairPrefix a b (i + 2 * l) c =
      2 * pairPrefix a b (i + l) c := by
    rw [pairPrefix_eq a b i (by omega), pairPrefix_eq a b (i + 2 * l) (by omega),
      pairPrefix_eq a b (i + l) (by omega)]
    exact count_prefix_square i l hp c
  exact hs (by have := hc 0; have := hc 1; have := hc 2; have := hc 3; omega)

end


/-! ### Upstream module `ErdosProblems/Erdos192/BlockDecomposition.lean` -/

section
theorem applyKeranenG_take_blocks (w : List (Fin 4)) (k s : ℕ)
    (hk : k < w.length) (hs : s ≤ 85) :
    (applyKeranenG w).take (85 * k + s) =
    applyKeranenG (w.take k) ++ (keranenG (w.get ⟨k, hk⟩)).take s := by
  induction' k with k ih generalizing w s
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ applyKeranenG ]
    · contradiction
    · exact Or.inr ( by rw [ keranenG_length ] ; linarith )
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ, List.take_append_of_le_length ]
    · contradiction
    · contradiction
    · simp_all +decide [ applyKeranenG ]
      rw [ ← ih ]
      · simp +arith +decide [ List.take_append, keranenG_length ]
      · grind
      · grind

end
section
theorem count_flatMap_sum {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → List β) (b : β) :
    (l.flatMap f).count b = (l.map (fun a => (f a).count b)).sum := by
  induction l <;> aesop

theorem applyKeranenG_append (l1 l2 : List (Fin 4)) :
    applyKeranenG (l1 ++ l2) = applyKeranenG l1 ++ applyKeranenG l2 := by
  simp [applyKeranenG, List.flatMap_append]

/-! ### List splitting -/


theorem count_take_split_head (w : List (Fin 4)) (k : ℕ) (c : Fin 4)
    (hk : 1 ≤ k) (hkw : k ≤ w.length) :
    (applyKeranenG (w.take k)).count c =
    (keranenG (w.get ⟨0, by omega⟩)).count c +
    (applyKeranenG (w.drop 1 |>.take (k - 1))).count c := by
  cases w with
  | nil => simp at hkw; omega
  | cons a w =>
    cases k with
    | zero => omega
    | succ k => simp [applyKeranenG, List.count_append]

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
      43435 * (if c = d then 1 else 0) := by decide +kernel

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
    (hm_ge : w.length ≥ 3) (hL : L > 0) (hr : r < 85)
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
          convert applyKeranenG_take_blocks w 0 r (by omega) hr.le using 1 <;> simp [applyKeranenG]
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
    split_ifs <;> simp_all +decide [ List.take_of_length_le ];
    · rw [ show ( 2 * ( ( r + L ) % 85 ) + 85000 - r ) % 85 = 0 from ?_ ] ; norm_num ; ring;
      · rw [ show List.take 85 ( keranenG w[0] ) = keranenG w[0] from ?_, show List.take 85 ( keranenG w[w.length - 1] ) = keranenG w[w.length - 1] from ?_ ] at * <;> norm_num at *;
        · rw [ show List.take 85 ( keranenG w[(r + L) / 85] ) = keranenG w[(r + L) / 85] from ?_ ] at * ; norm_num at *;
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

end


/-! ### Upstream module `ErdosProblems/Erdos192/ScalarData.lean` -/

section
def scalarData : Array (Array Int) :=
  #[
    #[0, -701, -1232, 2827, 2126, 6185, 3869, 7928, 7397, 11456, 9140, 13199, 12498, 10182, 14241, 11925, 11394, 9078, 8377, 7846, 7145, 11204, 10503, 9972, 9271, 6955, 6424, 5723, 5192, 9251, 8720, 6404, 5873, 9932, 9401, 8700, 12759, 12228, 16287, 13971, 18030, 17329, 21388, 20857, 20156, 19625, 17309, 16608, 16077, 15376, 19435, 18734, 16418, 20477, 19946, 24005, 21689, 25748, 25047, 29106, 26790, 26259, 30318, 29787, 29086, 33145, 32614, 36673, 34357, 38416, 37715, 41774, 39458, 43517, 42986, 40670, 44729, 42413, 41712, 39396, 38865, 36549, 40608, 40077, 44136, 43435],
    #[0, -531, 3528, 1212, 681, -1635, -2336, -4652, -593, -2909, -3610, -5926, -6457, -7158, -9474, -10175, -6116, -6817, -7348, -3289, -3820, -6136, -6667, -2608, -3139, -3840, 219, -312, 3747, 1431, 5490, 4789, 8848, 6532, 10591, 10060, 7744, 11803, 9487, 8786, 6470, 5939, 3623, 7682, 7151, 11210, 10509, 9978, 14037, 13506, 11190, 10659, 9958, 7642, 11701, 9385, 8684, 6368, 5837, 3521, 2820, 6879, 4563, 8622, 8091, 5775, 9834, 7518, 6817, 4501, 3970, 1654, 953, -1363, 2696, 1995, -321, -1022, -1553, -2254, 1805, 1104, -1212, 2847, 531, 0],
    #[0, 4059, 1743, 1042, 5101, 4400, 3869, 3168, 852, 151, -380, -1081, 2978, 2447, 1746, 1215, -1101, -1632, 2427, 111, 4170, 3469, 7528, 5212, 9271, 8740, 6424, 10483, 8167, 7466, 5150, 4619, 2303, 1602, -714, 3345, 2644, 328, -373, -904, -1605, 2454, 1753, -563, 3496, 1180, 649, 4708, 2392, 6451, 5750, 9809, 9278, 8577, 6261, 5560, 5029, 4328, 8387, 7686, 7155, 4839, 4138, 1822, 5881, 5180, 2864, 2163, 1632, 931, 4990, 4289, 3758, 3057, 741, 210, -491, -1022, 3037, 2506, 190, -341, -1042, -3358, -4059, 0],
    #[0, -2316, -3017, -3548, -5864, -6395, -2336, -2867, -3568, -4099, -40, -571, -2887, 1172, 641, 4700, 3999, 8058, 5742, 5041, 2725, 2194, -122, -823, -3139, 920, 219, -2097, -2798, -3329, -4030, 29, -672, -1203, -1904, -4220, -4751, -5452, -5983, -1924, -2455, -4771, -5302, -6003, -8319, -9020, -4961, -7277, -7978, -10294, -10825, -13141, -9082, -9613, -10314, -10845, -6786, -7317, -9633, -10164, -6105, -6806, -7337, -8038, -10354, -10885, -11586, -12117, -8058, -8589, -10905, -11436, -7377, -7908, -8609, -4550, -5081, -1022, -3338, 721, 20, 4079, 3548, 2847, 2316, 0]
  ]

def scalarPrefix (a : Fin 4) (k : Nat) : Int := (scalarData[a.val]!).getD k 0

theorem scalarData_correct : ∀ a : Fin 4, ∀ k : Fin 86,
    scalarPrefix a k.val = -701 * (fastPrefix a k.val 0 : Int) -
      531 * fastPrefix a k.val 1 + 4059 * fastPrefix a k.val 2 -
      2316 * fastPrefix a k.val 3 := by decide +kernel

end


/-! ### Upstream module `ErdosProblems/Erdos192/BoundaryFast.lean` -/

section
def fastDelta (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  (fastPrefix wb 85 c : Int) - fastPrefix wb s c +
  fastPrefix we ((2 * s + 85000 - r) % 85) c - fastPrefix we 0 c -
  ((fastPrefix wa 85 c : Int) - fastPrefix wa r c) -
  ((fastPrefix wb s c : Int) - fastPrefix wb 0 c)

def fastAdj (wa wb we : Fin 4) (r s : Nat) (c : Fin 4) : Int :=
  let d := fastDelta wa wb we r s
  match c with
  | 0 => -701 * d 0 + (-531) * d 1 + 4059 * d 2 + (-2316) * d 3
  | 1 => (-2316) * d 0 + (-701) * d 1 + (-531) * d 2 + 4059 * d 3
  | 2 => 4059 * d 0 + (-2316) * d 1 + (-701) * d 2 + (-531) * d 3
  | 3 => (-531) * d 0 + 4059 * d 1 + (-2316) * d 2 + (-701) * d 3

theorem fastDelta_eq (wa wb we : Fin 4) (r s : Fin 85) (c : Fin 4) :
    fastDelta wa wb we r.val s.val c = boundaryDelta wa wb we r.val s.val c := by
  unfold fastDelta boundaryDelta sliceParikhCount
  simp only [prefixData_correct wa ⟨85, by decide⟩ c,
    prefixData_correct wb ⟨85, by decide⟩ c,
    prefixData_correct wb ⟨s.val, by omega⟩ c,
    prefixData_correct wa ⟨r.val, by omega⟩ c,
    prefixData_correct wb ⟨0, by decide⟩ c,
    prefixData_correct we ⟨0, by decide⟩ c,
    prefixData_correct we ⟨(2 * s.val + 85000 - r.val) % 85, by omega⟩ c]
  ring

theorem fastAdj_eq (wa wb we : Fin 4) (r s : Fin 85) (c : Fin 4) :
    fastAdj wa wb we r.val s.val c = adjMTtimesDelta wa wb we r.val s.val c := by
  fin_cases c <;> simp only [fastAdj, adjMTtimesDelta, fastDelta_eq]

def scalarDelta (wa wb we : Fin 4) (r s : Nat) : Int :=
  scalarPrefix wb 85 - scalarPrefix wa 85 + scalarPrefix wa r +
    scalarPrefix we ((2 * s + 85000 - r) % 85) - 2 * scalarPrefix wb s

theorem scalarDelta_eq (wa wb we : Fin 4) (r s : Fin 85) :
    scalarDelta wa wb we r.val s.val = fastAdj wa wb we r.val s.val 0 := by
  unfold scalarDelta
  rw [scalarData_correct wb ⟨85, by decide⟩, scalarData_correct wa ⟨85, by decide⟩,
    scalarData_correct wa ⟨r.val, by omega⟩,
    scalarData_correct we ⟨(2 * s.val + 85000 - r.val) % 85, by omega⟩,
    scalarData_correct wb ⟨s.val, by omega⟩]
  have hz : ∀ a c : Fin 4, fastPrefix a 0 c = 0 := by decide +kernel
  simp only [fastAdj, fastDelta, hz, Nat.cast_zero, sub_zero]
  ring

def boundaryCheck (wa wb we : Fin 4) (r s : Fin 85) : Bool :=
  let a := fastAdj wa wb we r.val s.val
  if scalarDelta wa wb we r.val s.val % 43435 != 0 then true else
    let v := fun c => a c / 43435
    vGivesSomeAS wa wb we v &&
      (if (2 * s.val + 85000 - r.val) % 85 == 0 then
        vGivesSomeAS wa wb we (fun c => v c + if c = we then 1 else 0)
       else true)

end


/-! ### Upstream module `ErdosProblems/Erdos192/Bitset.lean` -/

section
def bitset : List Nat → Nat
  | [] => 0
  | x :: xs => (1 <<< x) ||| bitset xs

theorem testBit_bitset (xs : List Nat) (i : Nat) :
    (bitset xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [bitset]
  | cons x xs ih =>
    simp only [bitset, Nat.testBit_or, Bool.or_eq_true, List.mem_cons]
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq, ih]
    simp [eq_comm]

def rotateMask (m bits q : Nat) : Nat :=
  ((bits <<< q) ||| (bits >>> (m - q))) % (2 ^ m)

theorem rotateMask_contains (m bits q i : Nat) (hm : 0 < m) (hq : q < m)
    (hi : i < m) (h : bits.testBit i = true) :
    (rotateMask m bits q).testBit ((i + q) % m) = true := by
  unfold rotateMask
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨Nat.mod_lt _ hm, ?_⟩
  rw [Bool.or_eq_true]
  by_cases hlt : i + q < m
  · left
    rw [Nat.mod_eq_of_lt hlt, Nat.testBit_shiftLeft]
    simp [h]
  · right
    rw [Nat.testBit_shiftRight]
    have hmod : (i + q) % m = i + q - m := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show m - q + (i + q - m) = i by omega]
    exact h

theorem mask_intersection_mem (left right : Nat) (xs : List Nat) (i : Nat)
    (h : left &&& right = bitset xs) (hl : left.testBit i = true)
    (hr : right.testBit i = true) : i ∈ xs := by
  apply (testBit_bitset xs i).mp
  rw [← h, Nat.testBit_and, hl, hr]
  rfl

end


/-! ### Upstream module `ErdosProblems/Erdos192/BoundaryMaskData.lean` -/

section
def positiveMasks : Array Nat :=
  #[0x4000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000004000000000000000000000000000000008000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000040000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000001000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000080000800000000000000000000000000100000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100001000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000100000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000001,
    0x80400000000000000000000000000000000000000000000000000010000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000001000000000000000000000000000000000000000000000004000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000800000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000008000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000800008000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000001000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000080000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000040000400000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000004000000000000000000000000100000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000004000000000400000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000008000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000004000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000008000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000008000000000000000000000000000000800000000000000000000001020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000001000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000020000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000001000000000000000000000000001000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000001,
    0x4000000040800000000000000000000000000100000000000000000100000000000000000000000000000000000002000000000000000000000000000000000000000000000008000000000000000000000000000020000200000000040000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000200000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000010000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000010000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000004000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000100000004000000000002000000000000000002000000000400000000000000000000000000000000000008000000000000000000000000000000010000000000000000000000800000000000000000000000000000000000000000000000000000100000000000000000100000000020000000000000000000000000000040000000400000000000000000008000000000000000000000000000000000000000000000020000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000010000002000000000000000000000000000000200000000000000000000000000000000000000000001000000000000000000000000000200002000000000000004000000000000000000000000000100000000000000000000000000000000000000000000000000000010000000000000000000000000000000000400000000000040800008000000010000000000000000000000800000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000002048000000000000000000000000001000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000010000000000000000000000000000000000400000000000000000000000000080000000000000000001000000000000000000000000000200000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000040000400000000080000000008000000000000000000000000001,
    0x8000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000080000000000000000000000000000000000001000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800008000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000080000800000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000100001000000000000000000000000000000004000000000000000000000000000001000000000000000000000000000000000000000000000004020000000000000000000000000000000000000000000000000000800008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000001000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000100001000000000000000000000000000000000000000000000004000000000000000000000000000004000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000001000010000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000400004000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000200000000000000200002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000400004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000200002000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000400000000040000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000002000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000020100001]

def negativeMasks : Array Nat :=
  #[0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000800008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000080000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000800000000000000000000000000100001000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000002000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000010000000000000000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001,
    0x10000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000080000000000000000000000000080000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000004000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000080000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004080000000000000000000000100000000000000000000000000000010000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000010000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000010000000000000004000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000040000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000200000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000800000000000000000000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000200002000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000001000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000080000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000010000100000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000010000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000080000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000100000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000020000000000000000000000000000000000000000000000080000000000000000000000000000000000001000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000008000000000000000000000000000000000000000000000000000201000000000000000000000000000000000000000000000000000000000000000000000000000001,
    0x10000000001000000000200002000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000400000000000000000000000000080000000000000000001000000000000000000000000000200000000000000000000000000000000008000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000080000000000000000000000000012040000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000100000000000000000000008000000010000102000000000000200000000000000000000000000000000008000000000000000000000000000000000000000000000000000000800000000000000000000000000020000000000000040000400000000000000000000000000080000000000000000000000000000000000000000000400000000000000000000000000000040000008000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000004000000000000000000000000000000000000000000000010000000000000000000200000002000000000000000000000000000004000000000800000000000000000800000000000000000000000000000000000000000000000000000100000000000000000000008000000000000000000000000000000010000000000000000000000000000000000000200000000040000000000000000040000000000020000000800000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000020000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000008000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000008000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000400000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200002000000000400004000000000000000000000000000010000000000000000000000000000000000000000000000040000000000000000000000000000000000000800000000000000000800000000000000000000000000102000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000001,
    0x804000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000040000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200002000000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000040000400000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000200000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000040000400000000000000400000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000020000200000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000008000080000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000020000000000000000000000000000020000000000000000000000000000000000000000000000080000800000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000080000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000100000000000000000000000000000000000000000000000000004020000000000000000000000000000000000000000000000080000000000000000000000000000020000000000000000000000000000000080000800000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000000100001000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000010000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000080000000000000000000000000000000000001000000000000000000000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000010000000001]

def boundaryCandidates : Array (Array (List Nat)) :=
  #[
    #[[0, 1, 3, 17, 68, 82, 84], [1], [2], [3], [4, 23, 24, 69, 70], [5], [6, 22, 75], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57], [58], [59], [60], [61], [62], [63], [64], [65], [66], [67], [68], [69], [70], [71], [72], [73], [74], [75], [76], [77], [11, 14, 57, 60, 78], [79], [80], [81], [82], [83], [84]],
    #[[0], [], [], [4, 5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [44, 45, 51, 52], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [72], [], [77, 78, 79], [72], [], [81], [], [], [], []],
    #[[0], [77, 80], [], [], [69, 73], [], [6], [9], [], [], [], [], [], [], [], [], [], [], [], [], [10, 17], [14, 15], [], [21], [24], [9], [26], [], [], [], [35, 37, 39, 41], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [70], [73, 74], [77], [], [], [], [], [], [83], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [61], [45, 47, 48, 56], [], [53, 64], [], [65, 66, 67], [57], [62], [], [], [67, 70], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [51], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [68, 74], [], [75, 76, 77], [], [1, 3], [2], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [10, 63], [], [4, 5, 6, 7, 12, 65, 70, 71, 72, 73], [1, 15, 64, 78], [], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [12, 20, 21, 23], [], [8, 19], [], [9, 10, 11], [21], [18], [], [], [16, 19], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [69], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [76, 82], [], [77, 78, 79], [], [70, 72], [73], [], [], [], []],
    #[[0], [], [8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [75], [74], [74], [71], [], [5, 76], [79]],
    #[[0], [77], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [75, 76, 77], [], [], [76], [], [4, 5], [], [12]],
    #[[0, 1, 3, 17, 68, 82, 84], [10, 77], [], [], [14, 15, 78, 79], [], [6, 22, 75], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [24], [], [26], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [83], [2, 81]],
    #[[0], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77, 78, 79], [], [], [84], [], [74, 75], [], [71]],
    #[[0], [7, 10], [], [], [20, 24], [], [6], [5], [], [], [], [], [], [], [], [], [], [], [], [], [23, 30], [27, 28], [], [25], [24], [41], [26], [], [], [], [19, 21, 23, 25], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [80], [78, 79], [77], [], [], [], [], [], [83], []],
    #[[0], [8, 9, 10, 11], [16], [34], [13], [45, 48], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [34, 35], [], [], [], [], [], [75, 76, 77], [], [], [], [], [], [], [78, 80]],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [], [8, 16, 67, 75]],
    #[[0], [76, 77, 78, 79], [73], [57], [80], [47, 50], [], [], [], [], [], [], [], [], [], [], [], [], [], [34], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [22, 23], [], [], [], [], [], [77, 78, 79], [], [], [], [], [], [], [3, 5]],
    #[[0], [], [81], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [81], [84], [1], [6], [], [5, 76], [4]],
    #[[0], [], [], [1, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10, 11, 17, 18], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [78], [], [75, 76, 77], [84], [], [79], [], [], [], []],
    #[[0], [], [], [1, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10, 11, 17, 18], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [78], [], [75, 76, 77], [84], [], [79], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [], [8, 16, 67, 75]],
    #[[0], [76, 77, 78, 79], [73], [57], [80], [47, 50], [], [], [], [], [], [], [], [], [], [], [], [], [], [34], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [22, 23], [], [], [], [], [], [77, 78, 79], [], [], [], [], [], [], [3, 5]],
    #[[0], [], [81], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [81], [84], [1], [6], [], [5, 76], [4]],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [61], [45, 47, 48, 56], [], [53, 64], [], [65, 66, 67], [57], [62], [], [], [67, 70], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [51], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [68, 74], [], [75, 76, 77], [], [1, 3], [2], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [1], [2], [3], [4, 23, 24, 69, 70], [5], [6, 22, 75], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57], [58], [59], [60], [61], [62], [63], [64], [65], [66], [67], [68], [69], [70], [71], [72], [73], [74], [75], [76], [77], [11, 14, 57, 60, 78], [79], [80], [81], [82], [83], [84]],
    #[[0], [], [], [4, 5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [44, 45, 51, 52], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [72], [], [77, 78, 79], [72], [], [81], [], [], [], []],
    #[[0], [77, 80], [], [], [69, 73], [], [6], [9], [], [], [], [], [], [], [], [], [], [], [], [], [10, 17], [14, 15], [], [21], [24], [9], [26], [], [], [], [35, 37, 39, 41], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [70], [73, 74], [77], [], [], [], [], [], [83], []],
    #[[0], [77], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [75, 76, 77], [], [], [76], [], [4, 5], [], [12]],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [10, 63], [], [4, 5, 6, 7, 12, 65, 70, 71, 72, 73], [1, 15, 64, 78], [], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [12, 20, 21, 23], [], [8, 19], [], [9, 10, 11], [21], [18], [], [], [16, 19], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [69], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [76, 82], [], [77, 78, 79], [], [70, 72], [73], [], [], [], []],
    #[[0], [], [8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [75], [74], [74], [71], [], [5, 76], [79]],
    #[[0], [8, 9, 10, 11], [16], [34], [13], [45, 48], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [34, 35], [], [], [], [], [], [75, 76, 77], [], [], [], [], [], [], [78, 80]],
    #[[0, 1, 3, 17, 68, 82, 84], [10, 77], [], [], [14, 15, 78, 79], [], [6, 22, 75], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [24], [], [26], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [83], [2, 81]],
    #[[0], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77, 78, 79], [], [], [84], [], [74, 75], [], [71]],
    #[[0], [7, 10], [], [], [20, 24], [], [6], [5], [], [], [], [], [], [], [], [], [], [], [], [], [23, 30], [27, 28], [], [25], [24], [41], [26], [], [], [], [19, 21, 23, 25], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [80], [78, 79], [77], [], [], [], [], [], [83], []],
    #[[0], [7, 10], [], [], [20, 24], [], [6], [5], [], [], [], [], [], [], [], [], [], [], [], [], [23, 30], [27, 28], [], [25], [24], [41], [26], [], [], [], [19, 21, 23, 25], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [80], [78, 79], [77], [], [], [], [], [], [83], []],
    #[[0], [8, 9, 10, 11], [16], [34], [13], [45, 48], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [34, 35], [], [], [], [], [], [75, 76, 77], [], [], [], [], [], [], [78, 80]],
    #[[0, 1, 3, 17, 68, 82, 84], [10, 77], [], [], [14, 15, 78, 79], [], [6, 22, 75], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [24], [], [26], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [83], [2, 81]],
    #[[0], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77, 78, 79], [], [], [84], [], [74, 75], [], [71]],
    #[[0], [], [81], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [81], [84], [1], [6], [], [5, 76], [4]],
    #[[0], [], [], [1, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10, 11, 17, 18], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [78], [], [75, 76, 77], [84], [], [79], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [], [8, 16, 67, 75]],
    #[[0], [76, 77, 78, 79], [73], [57], [80], [47, 50], [], [], [], [], [], [], [], [], [], [], [], [], [], [34], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [22, 23], [], [], [], [], [], [77, 78, 79], [], [], [], [], [], [], [3, 5]],
    #[[0], [77, 80], [], [], [69, 73], [], [6], [9], [], [], [], [], [], [], [], [], [], [], [], [], [10, 17], [14, 15], [], [21], [24], [9], [26], [], [], [], [35, 37, 39, 41], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [70], [73, 74], [77], [], [], [], [], [], [83], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [61], [45, 47, 48, 56], [], [53, 64], [], [65, 66, 67], [57], [62], [], [], [67, 70], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [51], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [68, 74], [], [75, 76, 77], [], [1, 3], [2], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [1], [2], [3], [4, 23, 24, 69, 70], [5], [6, 22, 75], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57], [58], [59], [60], [61], [62], [63], [64], [65], [66], [67], [68], [69], [70], [71], [72], [73], [74], [75], [76], [77], [11, 14, 57, 60, 78], [79], [80], [81], [82], [83], [84]],
    #[[0], [], [], [4, 5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [44, 45, 51, 52], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [72], [], [77, 78, 79], [72], [], [81], [], [], [], []],
    #[[0], [], [8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [75], [74], [74], [71], [], [5, 76], [79]],
    #[[0], [77], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [75, 76, 77], [], [], [76], [], [4, 5], [], [12]],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [10, 63], [], [4, 5, 6, 7, 12, 65, 70, 71, 72, 73], [1, 15, 64, 78], [], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [12, 20, 21, 23], [], [8, 19], [], [9, 10, 11], [21], [18], [], [], [16, 19], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [69], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [76, 82], [], [77, 78, 79], [], [70, 72], [73], [], [], [], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [5], [12, 20, 21, 23], [], [8, 19], [], [9, 10, 11], [21], [18], [], [], [16, 19], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [69], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [76, 82], [], [77, 78, 79], [], [70, 72], [73], [], [], [], []],
    #[[0], [], [8], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [75], [74], [74], [71], [], [5, 76], [79]],
    #[[0], [77], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [75, 76, 77], [], [], [76], [], [4, 5], [], [12]],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [10, 63], [], [4, 5, 6, 7, 12, 65, 70, 71, 72, 73], [1, 15, 64, 78], [], []],
    #[[0], [10], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77, 78, 79], [], [], [84], [], [74, 75], [], [71]],
    #[[0], [7, 10], [], [], [20, 24], [], [6], [5], [], [], [], [], [], [], [], [], [], [], [], [], [23, 30], [27, 28], [], [25], [24], [41], [26], [], [], [], [19, 21, 23, 25], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [80], [78, 79], [77], [], [], [], [], [], [83], []],
    #[[0], [8, 9, 10, 11], [16], [34], [13], [45, 48], [], [], [], [], [], [], [], [], [], [], [], [], [], [4], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [34, 35], [], [], [], [], [], [75, 76, 77], [], [], [], [], [], [], [78, 80]],
    #[[0, 1, 3, 17, 68, 82, 84], [10, 77], [], [], [14, 15, 78, 79], [], [6, 22, 75], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [24], [], [26], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [83], [2, 81]],
    #[[0], [76, 77, 78, 79], [73], [57], [80], [47, 50], [], [], [], [], [], [], [], [], [], [], [], [], [], [34], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [22, 23], [], [], [], [], [], [77, 78, 79], [], [], [], [], [], [], [3, 5]],
    #[[0], [], [81], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [81], [84], [1], [6], [], [5, 76], [4]],
    #[[0], [], [], [1, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [10, 11, 17, 18], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [78], [], [75, 76, 77], [84], [], [79], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [77], [], [], [], [], [], [], [8, 16, 67, 75]],
    #[[0], [], [], [4, 5], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [44, 45, 51, 52], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [72], [], [77, 78, 79], [72], [], [81], [], [], [], []],
    #[[0], [77, 80], [], [], [69, 73], [], [6], [9], [], [], [], [], [], [], [], [], [], [], [], [], [10, 17], [14, 15], [], [21], [24], [9], [26], [], [], [], [35, 37, 39, 41], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [70], [73, 74], [77], [], [], [], [], [], [83], []],
    #[[0], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [61], [45, 47, 48, 56], [], [53, 64], [], [65, 66, 67], [57], [62], [], [], [67, 70], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [51], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [68, 74], [], [75, 76, 77], [], [1, 3], [2], [], [], [], []],
    #[[0, 1, 3, 17, 68, 82, 84], [1], [2], [3], [4, 23, 24, 69, 70], [5], [6, 22, 75], [7], [8], [9], [10], [11], [12], [13], [14], [15], [16], [17], [18], [19], [20], [21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36], [37], [38], [39], [40], [41], [42], [43], [44], [45], [46], [47], [48], [49], [50], [51], [52], [53], [54], [55], [56], [57], [58], [59], [60], [61], [62], [63], [64], [65], [66], [67], [68], [69], [70], [71], [72], [73], [74], [75], [76], [77], [11, 14, 57, 60, 78], [79], [80], [81], [82], [83], [84]]
  ]

end


/-! ### Upstream module `ErdosProblems/Erdos192/BoundaryMaskCertificate.lean` -/

section
def residue (a : Fin 4) (r : Nat) : Nat := (scalarPrefix a r % 43435).toNat

def negativeResidue (a : Fin 4) (r : Nat) : Nat := (-scalarPrefix a r % 43435).toNat

def midpointResidue (a : Fin 4) (r : Nat) : Nat := (2 * scalarPrefix a r % 43435).toNat

def candidates (a b e : Fin 4) (s : Nat) : List Nat :=
  (boundaryCandidates[a.val * 16 + b.val * 4 + e.val]!).getD s []

def maskCheck (a b e : Fin 4) (s : Fin 85) : Bool :=
  (positiveMasks[a.val]! &&&
    rotateMask 43435 negativeMasks[e.val]! (midpointResidue b s.val)) ==
      bitset ((candidates a b e s.val).map (residue a))

def candidateCheck (a b e : Fin 4) (s : Fin 85) : Bool :=
  (candidates a b e s.val).all fun r =>
    if h : r < 85 then boundaryCheck a b e ⟨r, h⟩ s else false

def masksCertificate : Bool :=
  (List.finRange 4).all fun a =>
  (List.finRange 4).all fun b =>
  (List.finRange 4).all fun e =>
  (List.finRange 85).all fun s => maskCheck a b e s && candidateCheck a b e s

theorem masksCertificate_true : masksCertificate = true := by decide +kernel

theorem masksContainPrefixes : ∀ a : Fin 4, ∀ r : Fin 85,
    positiveMasks[a.val]!.testBit (residue a r.val) = true ∧
    negativeMasks[a.val]!.testBit (negativeResidue a r.val) = true := by decide +kernel

theorem scalarPrefix_mod85 : ∀ a : Fin 4, ∀ r : Fin 85,
    scalarPrefix a r.val % 85 = (64 * (r.val : Int)) % 85 := by decide +kernel

theorem scalarPrefix_full : ∀ a : Fin 4, scalarPrefix a 85 % 43435 = 0 := by
  decide +kernel

end


/-! ### Upstream module `ErdosProblems/Erdos192/BoundaryMasks.lean` -/

section

theorem residue_injective (a : Fin 4) (r t : Fin 85)
    (h : residue a r.val = residue a t.val) : r = t := by
  have hr := scalarPrefix_mod85 a r
  have ht := scalarPrefix_mod85 a t
  unfold residue at h
  have hn1 := Int.emod_nonneg (scalarPrefix a r.val) (by decide : (43435 : Int) ≠ 0)
  have hn2 := Int.emod_nonneg (scalarPrefix a t.val) (by decide : (43435 : Int) ≠ 0)
  have heq : scalarPrefix a r.val % 43435 = scalarPrefix a t.val % 43435 := by omega
  have heq' := congrArg (fun z : Int => z % 85) heq
  rw [Int.emod_emod_of_dvd _ (by decide : (85 : Int) ∣ 43435),
    Int.emod_emod_of_dvd _ (by decide : (85 : Int) ∣ 43435), hr, ht] at heq'
  apply Fin.ext
  omega

theorem modular_balance (A B x y z : Int)
    (hA : A % 43435 = 0) (hB : B % 43435 = 0)
    (h : (B - A + x + z - 2 * y) % 43435 = 0) :
    ((-z % 43435).toNat + (2 * y % 43435).toNat) % 43435 = (x % 43435).toNat := by
  have hAB : (B - A) % 43435 = 0 := by rw [Int.sub_emod, hA, hB]; rfl
  rw [show B - A + x + z - 2 * y = (B - A) + (x + z - 2 * y) by ring,
    Int.add_emod, hAB, Int.zero_add, Int.emod_emod] at h
  have heq : x % 43435 = (-z + 2 * y) % 43435 := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    convert h using 1 <;> congr 1 <;> ring
  have hn1 := Int.emod_nonneg (-z) (by decide : (43435 : Int) ≠ 0)
  have hn2 := Int.emod_nonneg (2 * y) (by decide : (43435 : Int) ≠ 0)
  have hn3 := Int.emod_nonneg x (by decide : (43435 : Int) ≠ 0)
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod, Int.natCast_add, Int.toNat_of_nonneg hn1,
    Int.toNat_of_nonneg hn2, Int.toNat_of_nonneg hn3]
  change (-z % 43435 + (2 * y) % 43435) % 43435 = x % 43435
  rw [← Int.add_emod]
  exact heq.symm

theorem scalarDelta_residues (a b e : Fin 4) (r s : Fin 85)
    (h : scalarDelta a b e r.val s.val % 43435 = 0) :
    (negativeResidue e ((2 * s.val + 85000 - r.val) % 85) +
      midpointResidue b s.val) % 43435 = residue a r.val :=
  modular_balance _ _ _ _ _ (scalarPrefix_full a) (scalarPrefix_full b) h

theorem boundaryCheck_verified (a b e : Fin 4) (r s : Fin 85) :
    boundaryCheck a b e r s = true := by
  by_cases h : scalarDelta a b e r.val s.val % 43435 = 0
  · have hcert := masksCertificate_true
    simp only [masksCertificate, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.and_eq_true] at hcert
    obtain ⟨hm, hc⟩ := hcert a b e s
    have ht : (2 * s.val + 85000 - r.val) % 85 < 85 := Nat.mod_lt _ (by decide)
    have hp := (masksContainPrefixes a r).1
    have he := (masksContainPrefixes e ⟨_, ht⟩).2
    have hq : midpointResidue b s.val < 43435 := by
      unfold midpointResidue
      have := Int.emod_lt_of_pos (2 * scalarPrefix b s.val) (by decide : (0 : Int) < 43435)
      omega
    have he' := rotateMask_contains 43435 negativeMasks[e.val]! (midpointResidue b s.val)
      (negativeResidue e ((2 * s.val + 85000 - r.val) % 85)) (by decide) hq (by
        unfold negativeResidue
        have := Int.emod_lt_of_pos (-scalarPrefix e ((2 * s.val + 85000 - r.val) % 85))
          (by decide : (0 : Int) < 43435)
        omega) he
    rw [scalarDelta_residues a b e r s h] at he'
    have hmem := mask_intersection_mem _ _ _ _ (beq_iff_eq.mp hm) hp he'
    obtain ⟨r', hr', heq⟩ := List.mem_map.mp hmem
    have hc' := List.all_eq_true.mp hc r' hr'
    split at hc'
    next hrlt =>
      have hr := residue_injective a ⟨r', hrlt⟩ r heq
      simpa only [hr] using hc'
    next hrlt => exact Bool.noConfusion hc'
  · simp [boundaryCheck, h]

end


/-! ### Upstream module `ErdosProblems/Erdos192/BoundaryCheck.lean` -/

section
theorem v_pattern_gives_AS_normal (wa wb we : Fin 4) (r s : Fin 85)
    (h : hasParikhSolution wa wb we r.val s.val = true) :
    vGivesSomeAS wa wb we (parikhSolutionVec wa wb we r.val s.val) = true := by
  have hv := boundaryCheck_verified wa wb we r s
  simp only [hasParikhSolution, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [boundaryCheck, scalarDelta_eq, fastAdj_eq, h.1.1.1,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hv
  exact hv.1

theorem v_pattern_gives_AS_t85 (wa wb we : Fin 4) (r s : Fin 85)
    (h : hasParikhSolution wa wb we r.val s.val = true)
    (ht : (2 * s.val + 85000 - r.val) % 85 = 0) :
    vGivesSomeAS wa wb we (fun c => parikhSolutionVec wa wb we r.val s.val c +
      if c = we then 1 else 0) = true := by
  have hv := boundaryCheck_verified wa wb we r s
  simp only [hasParikhSolution, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [boundaryCheck, scalarDelta_eq, fastAdj_eq, h.1.1.1,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
    ht, beq_self_eq_true] at hv
  exact hv.2

end


/-! ### Upstream module `ErdosProblems/Erdos192/Spanning.lean` -/

section
theorem inner_defect_gives_AS (w : List (Fin 4))
    (hm_ge : w.length ≥ 3) (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ 85 * w.length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    let k := (r + L) / 85
    let s := (r + L) % 85
    let m := w.length
    let t := r + 2 * L - 85 * (m - 1)
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
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 0;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 1;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 2;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 3;
  · convert v_pattern_gives_AS_normal w[0] w[(r + L) / 85] w[w.length - 1] ⟨r, hr⟩ ⟨(r + L) % 85, Nat.mod_lt _ (by decide)⟩ _ using 1;
    · unfold parikhSolutionVec; simp +decide [ *, adjMTtimesDelta_eq_adjRow ] ;
      congr! 2;
      exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by decide ) ( by linarith [ ‹∀ a : Fin 4, 43435 * ( ↑ ( List.count a ( List.take ( ( r + L ) / 85 - 1 ) w.tail ) ) - ↑ ( List.count a ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) ) ) = adjRow a ( boundaryDelta w[0] w[( r + L ) / 85] w[w.length - 1] r ( ( r + L ) % 85 ) ) › ‹_› ] ) );
    · unfold hasParikhSolution; simp +decide [ h_adj_solve ] ;
      exact ⟨ ⟨ ⟨ h_adj_solve 0, h_adj_solve 1 ⟩, h_adj_solve 2 ⟩, h_adj_solve 3 ⟩

/-! ### List counting helpers -/

theorem sum_count_eq_length (l : List (Fin 4)) :
    (l.count 0 : Int) + l.count 1 + l.count 2 + l.count 3 = l.length := by
  induction l <;> simp +decide [ * ] ; ring;
  rename_i k hk ih; fin_cases k <;> simp +decide [ List.count_cons ] at ih ⊢ <;> linarith;

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
  intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ List.take_succ_cons ] ;
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
    (hm : w.length ≥ 3)
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

end


/-! ### Upstream module `ErdosProblems/Erdos192/Localization.lean` -/

section
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

end


/-! ### Upstream module `ErdosProblems/Erdos192/Morphism.lean` -/

section
theorem morphism_preserves_le2 (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hlen : w.length ≤ 2) : FinAbelianSquareFree (applyKeranenG w) := by
  cases w with
  | nil => intro i l hl h; simp [applyKeranenG] at h; omega
  | cons a w =>
    cases w with
    | nil =>
      have hab : a ≠ a + 1 := by fin_cases a <;> decide
      have h := finASF_prefix (applyKeranenG [a, a + 1]) (keranen_pair_asf a (a + 1) hab)
        85 (by simp [applyKeranenG_length])
      simpa [applyKeranenG, List.take_append, keranenG_length,
        List.take_of_length_le (le_of_eq (keranenG_length a))] using h
    | cons b w =>
      cases w with
      | nil =>
        apply keranen_pair_asf a b
        intro hab
        subst b
        exact hw 0 1 (by decide) (by simp) (List.Perm.refl [a])
      | cons c w => simp at hlen

/-- Any square spanning at least three blocks descends to the preimage;
the remaining one- and two-block cases are checked by a streaming certificate. -/
theorem keranenG_preserves_ASF (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    FinAbelianSquareFree (applyKeranenG w) := by
  intro i L hL hlen hperm
  let a := i / 85
  let m := (i + 2 * L - 1) / 85 - a + 1
  let r := i % 85
  let w' := w.drop a |>.take m
  have ham : a + m ≤ w.length := by
    rw [applyKeranenG_length] at hlen
    dsimp [a, m]
    omega
  have hw' : FinAbelianSquareFree w' := finASF_subword w hw a m ham
  have hwlen : w'.length = m := by
    simp only [w', List.length_take, List.length_drop]
    omega
  obtain ⟨hlen', hperm'⟩ := abelianSquare_localize_explicit w i L hL hlen hperm
  have hspan : (r + 2 * L - 1) / 85 + 1 = w'.length := by
    rw [hwlen]
    exact localized_block_span w i L hL hlen
  by_cases hm : m ≤ 2
  · exact morphism_preserves_le2 w' hw' (by omega) r L hL hlen' hperm'
  · exact no_spanning_large w' hw' (by omega) r L hL
      (Nat.mod_lt _ (by decide)) hlen' hspan hperm'

end


/-! ### Upstream module `ErdosProblems/Erdos192/Infinite.lean` -/

section
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
      push Not at h_contra
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
      · rw [List.ofFn_succ_last]
        simpa only [Fin.val_castSucc, Fin.val_last, ← hf n] using hc _ ih
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

end


/-! ### Upstream module `ErdosProblems/Erdos192/Ternary.lean` -/

section
def isFinASF3 (word : List (Fin 3)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      let l := l + 1
      if i + 2 * l > word.length then false
      else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l))

/-- **3-letter ASF bound.** No ASF word on 3 letters has length ≥ 8. -/
theorem max_asf_3letters :
    ∀ a b c d e f g h : Fin 3,
      isFinASF3 [a, b, c, d, e, f, g, h] = false := by decide +kernel

theorem isFinASF3_complete (w : List (Fin 3)) (hw : FinAbelianSquareFree w) :
    isFinASF3 w = true := by
  unfold isFinASF3;
  simp +zetaDelta at *;
  intro i hi j hj hij; contrapose! hw;
  exact fun h => h i ( j + 1 ) ( Nat.succ_pos _ ) hij ( by simpa [ List.isPerm_iff ] using hw )

/-
`infBlock` of `e ∘ f` is the map of `infBlock` of `f`.
-/
theorem inf_asf_comp_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : ℕ → α) (e : α → β) (he : Function.Injective e)
    (hf : InfAbelianSquareFree f) : InfAbelianSquareFree (e ∘ f) := by
  intro i l hl; specialize hf i l hl; simp_all +decide [ InfAbelianSquareFree, List.map_eq_map_iff ] ;
  contrapose! hf;
  rw [ ← List.map_perm_map_iff he ];
  unfold infBlock at *; aesop;

/-
No infinite word over `Fin 3` is abelian-square-free.
Proof: by `max_asf_3letters`, every length-8 prefix has an abelian square.
-/
theorem no_inf_asf_three (f : ℕ → Fin 3) : ¬InfAbelianSquareFree f := by
  intro hf
  have h8 : FinAbelianSquareFree (infBlock f 0 8) := by
    -- For any i, l, if the two blocks of length l starting at i and i+l are permutations, then they are also permutations of the infinite word.
    intro i l hl h
    have := hf i l hl
    contrapose! this
    simp_all +decide [ infBlock ];
    convert this using 1;
    · refine' List.ext_get _ _ <;> simp +arith +decide [ List.get ];
      omega;
    · refine' List.ext_get _ _ <;> simp +arith +decide;
      omega;
  convert isFinASF3_complete _ h8 using 1;
  simp [infBlock];
  exact max_asf_3letters _ _ _ _ _ _ _ _

/-
For `d ≤ 3`, every infinite word over `Fin d` has a Parikh AP.
-/
theorem hasParikhAP_of_le_three {d : ℕ} (hd : d ≤ 3) (f : ℕ → Fin d) :
    hasParikhAP f := by
  -- Let `e := Fin.castLE hd : Fin d → Fin 3`. This is injective (Fin.castLE_injective).
  set e : Fin d → Fin 3 := fun x => Fin.castLE hd x
  have he_inj : Function.Injective e := by
    exact Fin.castLE_injective hd;
  -- If `InfAbelianSquareFree f`, then by `inf_asf_comp_inj`, `InfAbelianSquareFree (e ∘ f)`.
  by_cases h_inf_asf : InfAbelianSquareFree f;
  · exact False.elim <| no_inf_asf_three ( e ∘ f ) <| inf_asf_comp_inj f e he_inj h_inf_asf;
  · exact Classical.not_not.1 fun h => h_inf_asf <| by simpa [ h ] using infAbelianSquareFree_iff_parikhAPFree f |>.2 h;

end


/-! ### Upstream module `ErdosProblems/Erdos192/Geometry.lean` -/

section
/-- Positive standard-coordinate unit steps in real coordinate space. -/
def PositiveUnitWalk {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∀ n, ∃ i : Fin d, ∀ j, p (n + 1) j = p n j + if j = i then 1 else 0

/-- A nontrivial arithmetic progression, with its times in increasing order. -/
def HasWalkAP {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∃ a b c : ℕ, a < b ∧ b < c ∧ ∀ j, p a j + p c j = 2 * p b j

/-- The real Parikh walk with an arbitrary starting point. -/
def realWalk {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) (n : ℕ) (j : Fin d) : ℝ :=
  x j + parikhCount f n j

theorem parikhCount_succ {d : ℕ} (f : ℕ → Fin d) (n : ℕ) (j : Fin d) :
    parikhCount f (n + 1) j = parikhCount f n j + if j = f n then 1 else 0 := by
  by_cases h : j = f n
  · subst j
    simp [parikhCount, Finset.range_add_one, Finset.filter_insert]
  · simp [parikhCount, Finset.range_add_one, Finset.filter_insert, h, Ne.symm h]

theorem realWalk_positive {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    PositiveUnitWalk (realWalk x f) := by
  intro n
  refine ⟨f n, ?_⟩
  intro j
  simp only [realWalk, parikhCount_succ, Nat.cast_add]
  split_ifs <;> simp <;> ring

theorem positiveUnitWalk_representation {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : PositiveUnitWalk p) : ∃ f : ℕ → Fin d, p = realWalk (p 0) f := by
  classical
  choose f hf using hp
  refine ⟨f, funext fun n => funext fun j => ?_⟩
  induction n with
  | zero => simp [realWalk, parikhCount]
  | succ n ih =>
    rw [hf n j, ih]
    simp only [realWalk, parikhCount_succ, Nat.cast_add]
    split_ifs <;> simp <;> ring

theorem realWalk_hasAP_iff {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    HasWalkAP (realWalk x f) ↔ hasParikhAP f := by
  unfold HasWalkAP hasParikhAP
  constructor
  · rintro ⟨a, b, c, hab, hbc, h⟩
    refine ⟨a, b, c, hab, hbc, fun j => ?_⟩
    have hj := h j
    simp only [realWalk] at hj
    have : (parikhCount f a j : ℝ) + parikhCount f c j = 2 * parikhCount f b j := by
      linarith
    exact_mod_cast this
  · rintro ⟨a, b, c, hab, hbc, h⟩
    refine ⟨a, b, c, hab, hbc, fun j => ?_⟩
    have hj : (parikhCount f a j : ℝ) + parikhCount f c j = 2 * parikhCount f b j :=
      by exact_mod_cast h j
    simp only [realWalk]
    linarith

theorem geometric_classification_iff_words (d : ℕ) :
    (∀ p : ℕ → Fin d → ℝ, PositiveUnitWalk p → HasWalkAP p) ↔
      (∀ f : ℕ → Fin d, hasParikhAP f) := by
  constructor
  · intro h f
    exact (realWalk_hasAP_iff 0 f).mp (h _ (realWalk_positive 0 f))
  · intro h p hp
    obtain ⟨f, hf⟩ := positiveUnitWalk_representation p hp
    rw [hf]
    exact (realWalk_hasAP_iff _ f).mpr (h f)

theorem sum_parikhCount {d : ℕ} (f : ℕ → Fin d) (n : ℕ) :
    (∑ j : Fin d, parikhCount f n j) = n := by
  induction n with
  | zero => simp [parikhCount]
  | succ n ih => simp [parikhCount_succ, Finset.sum_add_distrib, ih]

theorem sum_realWalk {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) (n : ℕ) :
    (∑ j, realWalk x f n j) = (∑ j, x j) + n := by
  simp only [realWalk, Finset.sum_add_distrib]
  congr 1
  exact_mod_cast sum_parikhCount f n

theorem realWalk_injective {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    Function.Injective (realWalk x f) := by
  intro a b h
  have hs := congrArg (fun v : Fin d → ℝ => ∑ j, v j) h
  rw [sum_realWalk, sum_realWalk] at hs
  exact_mod_cast (add_left_cancel hs)

/-- The visited set contains three distinct points in arithmetic progression.
Only the first two need be required distinct: the equation forces the third. -/
def ContainsThreeTermAP {d : ℕ} (p : ℕ → Fin d → ℝ) : Prop :=
  ∃ x y z : Fin d → ℝ, x ∈ Set.range p ∧ y ∈ Set.range p ∧ z ∈ Set.range p ∧
    x ≠ y ∧ ∀ j, x j + z j = 2 * y j

theorem realWalk_setAP_iff {d : ℕ} (x : Fin d → ℝ) (f : ℕ → Fin d) :
    ContainsThreeTermAP (realWalk x f) ↔ HasWalkAP (realWalk x f) := by
  constructor
  · rintro ⟨_, _, _, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, hne, h⟩
    have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => h j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_realWalk] at hs
    have hn : (a : ℝ) + c = 2 * b := by linarith
    have hn' : a + c = 2 * b := by exact_mod_cast hn
    have hab : a ≠ b := fun hab => hne (congrArg (realWalk x f) hab)
    by_cases ht : a < b
    · exact ⟨a, b, c, ht, by omega, h⟩
    · exact ⟨c, b, a, by omega, by omega, fun j => by rw [add_comm]; exact h j⟩
  · rintro ⟨a, b, c, hab, hbc, h⟩
    exact ⟨_, _, _, ⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩,
      fun heq => (Nat.ne_of_lt hab) (realWalk_injective x f heq), h⟩

theorem positiveUnitWalk_setAP_iff {d : ℕ} (p : ℕ → Fin d → ℝ)
    (hp : PositiveUnitWalk p) : ContainsThreeTermAP p ↔ HasWalkAP p := by
  obtain ⟨f, hf⟩ := positiveUnitWalk_representation p hp
  rw [hf]
  exact realWalk_setAP_iff _ f

end

section

theorem exists_parikhAPFree_of_ge_four {d : ℕ} (hd : 4 ≤ d) :
    ∃ f : ℕ → Fin d, parikhAPFree f := by
  obtain ⟨f, hf⟩ := exists_inf_abelianSquareFree_four
  exact ⟨fun n => Fin.castLE hd (f n),
    (infAbelianSquareFree_iff_parikhAPFree _).mp
      (inf_asf_comp_inj f (Fin.castLE hd) (Fin.castLE_injective hd) hf)⟩

theorem erdos_problem_192_classification (d : ℕ) :
    (∀ f : ℕ → Fin d, hasParikhAP f) ↔ d ≤ 3 := by
  constructor
  · intro h
    by_contra hd
    obtain ⟨f, hf⟩ := exists_parikhAPFree_of_ge_four (by omega : 4 ≤ d)
    exact hf (h f)
  · exact fun hd f => hasParikhAP_of_le_three hd f

/-- Every positive unit walk has a nontrivial progression in its visited set
exactly in dimensions at most three. At dimension zero there are no such walks. -/
theorem erdos_192 (d : ℕ) :
    (∀ p : ℕ → Fin d → ℝ, PositiveUnitWalk p →
      ∃ x y z : Fin d → ℝ, x ∈ Set.range p ∧ y ∈ Set.range p ∧ z ∈ Set.range p ∧
        x ≠ y ∧ ∀ j, x j + z j = 2 * y j) ↔ d ≤ 3 := by
  rw [← erdos_problem_192_classification d, ← geometric_classification_iff_words d]
  exact forall_congr' fun p => imp_congr_right fun hp => positiveUnitWalk_setAP_iff p hp

end

#print axioms erdos_192
-- 'Erdos192.erdos_192' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos192
