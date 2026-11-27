import Mathlib

namespace Erdos1219

/-
# Erdős Problem 1219

Let $(n_k)$ be an increasing sequence of integers such that $2^{\aleph_{n_k}}$ is strictly
increasing, and $2^{\aleph_{n_0}}>\aleph_\omega$. Is it true that
$$\sum_{k} 2^{\aleph_{n_k}}\to (\aleph_\omega)^2?$$

The answer is **yes**, proved by Shelah [Sh75]. `erdos_1219` states it with
`PartitionArrow κ α` the binary partition relation $\kappa \to (\alpha)^2_2$: every
$2$-colouring of the $2$-element subsets of a set of cardinality $\kappa$ has a monochromatic
subset of cardinality $\alpha$. This is the binary case of `Combinatorics.cardinalPartitionRel`
in `formal-conjectures`. The proof follows Shelah's canonization lemma, with an unbalanced
Erdős--Rado theorem $(2^\mu)^+ \to ((2^\mu)^+, \mu^+)^2$ proved along the way.

Formalised by Ji Ho Bae in `jbaelaw/erdos1219-lean`; the six modules forming the closure of
`erdos_1219` are flattened here in dependency order. The upstream comparator files
(`Challenge.lean`, `Solution.lean`) are outside that closure and are not included.

Declarations that `erdos_1219` does not depend on have been removed.
-/

universe u

/-! ### Upstream module `Erdos1219/Defs.lean` -/

section
/-!
# Erdős problem #1219 — basic definitions

Pair colourings are represented by (symmetric) functions `f : V → V → Bool`;
only the values on pairs of distinct points matter.
-/

open _root_.Cardinal

variable {V : Type u}

/-- `H` is `c`-homogeneous for the pair colouring `f`: all pairs of distinct points of `H`
receive colour `c`. -/
def Homog (f : V → V → Bool) (c : Bool) (H : Set V) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → f x y = c

theorem Homog.mono {f : V → V → Bool} {c : Bool} {H H' : Set V} (h : Homog f c H)
    (hH : H' ⊆ H) : Homog f c H' :=
  fun x hx y hy hxy => h x (hH hx) y (hH hy) hxy

theorem Homog.empty (f : V → V → Bool) (c : Bool) : Homog f c ∅ := by
  intro x hx; simp at hx

/-- The pair colouring on ordered pairs of distinct points induced by a colouring of
`2`-element finsets (the diagonal is coloured `false`, which is irrelevant). -/
noncomputable def ofFinsetColouring (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    Bool := by
  classical
  exact if h : x = y then false else col ⟨{x, y}, Finset.card_pair h⟩

theorem ofFinsetColouring_apply [DecidableEq V] (col : {s : Finset V // s.card = 2} → Bool)
    {x y : V} (h : x ≠ y) :
    ofFinsetColouring col x y = col ⟨{x, y}, Finset.card_pair h⟩ := by
  unfold ofFinsetColouring
  simp only [h, ↓reduceDIte]
  congr
  exact Subsingleton.elim _ _

theorem ofFinsetColouring_symm (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    ofFinsetColouring col x y = ofFinsetColouring col y x := by
  classical
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun e => h e.symm
    rw [ofFinsetColouring_apply col h, ofFinsetColouring_apply col h']
    congr 1
    exact Subtype.ext (Finset.pair_comm x y)

/-- The classical binary partition relation `κ → (α)²₂` on colourings of `2`-element finsets,
in the style of `Combinatorics.cardinalPartitionRel` of formal-conjectures. -/
def PartitionArrow (κ α : Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = κ →
    ∀ col : {s : Finset A // s.card = 2} → Bool,
      ∃ (c : Bool) (H : Set A), #H = α ∧
        ∀ (s : Finset A) (hs : s.card = 2), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = c

end

/-! ### Upstream module `Erdos1219/CardinalLemmas.lean` -/

section
/-!
# Cardinal arithmetic lemmas for Erdős #1219

Small facts about regular cardinals, bounded subsets, `ℕ`-indexed sums and `ℵ_ω`.
-/

open _root_.Cardinal Ordinal _root_.Function

/-- A union of fewer than `c` sets, each of cardinality `< c`, has cardinality `< c` when `c`
is regular. -/
theorem mk_iUnion_lt_of_isRegular {V ι : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (hι : #ι < c) (t : ι → Set V) (ht : ∀ i, #(t i) < c) : #(⋃ i, t i) < c :=
  mk_iUnion_le_sum_mk.trans_lt (sum_lt_of_isRegular hc hι ht)

/-- Pigeonhole for regular cardinals: a set of regular cardinality `c` mapped into a type of
cardinality `< c` has a fibre of cardinality `c`. -/
theorem exists_fiber_eq_of_isRegular {V T : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (s : Set V) (hs : #s = c) (φ : V → T) (hT : #T < c) :
    ∃ t, #(s ∩ φ ⁻¹' {t} : Set V) = c := by
  by_contra h
  have hlt : ∀ t, #(s ∩ φ ⁻¹' {t} : Set V) < c := fun t =>
    lt_of_le_of_ne ((mk_le_mk_of_subset Set.inter_subset_left).trans_eq hs)
      (fun ht => h ⟨t, ht⟩)
  have hsub : s ⊆ ⋃ t, s ∩ φ ⁻¹' {t} := fun v hv => Set.mem_iUnion.2 ⟨φ v, hv, rfl⟩
  exact absurd ((mk_le_mk_of_subset hsub).trans_lt (mk_iUnion_lt_of_isRegular hc hT _ hlt))
    (by rw [hs]; exact lt_irrefl c)

theorem two_pow_pow_self {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    ((2 : Cardinal.{u}) ^ μ) ^ μ = 2 ^ μ := by
  rw [← power_mul, mul_eq_self hμ]

theorem le_two_pow_self {μ : Cardinal.{u}} : μ ≤ 2 ^ μ := (cantor μ).le

theorem aleph0_le_two_pow {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : ℵ₀ ≤ 2 ^ μ :=
  hμ.trans le_two_pow_self

/-- The subsets of `U` of cardinality `≤ μ`, when `#U ≤ 2 ^ μ`: there are at most `2 ^ μ`. -/
theorem mk_bounded_subsets_le {V : Type u} (U : Set V) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hU : #U ≤ 2 ^ μ) : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ 2 ^ μ := by
  have key : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ #{t : Set (↥U) // #t ≤ μ} := by
    refine mk_le_of_injective (f := fun B => ⟨Subtype.val ⁻¹' B.1, ?_⟩) ?_
    · rw [mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective
        (by simpa using B.2.1)]
      exact B.2.2
    · rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
      simp only [Subtype.mk.injEq] at h
      have h1 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) = B :=
        Set.image_preimage_eq_of_subset (by simpa using hB.1)
      have h2 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') = B' :=
        Set.image_preimage_eq_of_subset (by simpa using hB'.1)
      rw [Subtype.mk.injEq]
      calc B = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) := h1.symm
        _ = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') := by rw [h]
        _ = B' := h2
  refine key.trans ((mk_bounded_set_le (↥U) μ).trans ?_)
  have hmax : max #U ℵ₀ ≤ 2 ^ μ := max_le hU (aleph0_le_two_pow hμ)
  exact (power_le_power_right hmax).trans (two_pow_pow_self hμ).le

/-- The shift of an `ℕ`-indexed family has a smaller sum. -/
theorem sum_shift_le (a : ℕ → Cardinal.{u}) :
    Cardinal.sum (fun k => a (k + 1)) ≤ Cardinal.sum a := by
  show #(Σ k : ℕ, (a (k + 1)).out) ≤ #(Σ k : ℕ, (a k).out)
  refine mk_le_of_injective
    (f := fun p : (Σ k : ℕ, (a (k + 1)).out) => (⟨p.1 + 1, p.2⟩ : Σ k : ℕ, (a k).out)) ?_
  rintro ⟨k, x⟩ ⟨k', x'⟩ h
  simp only [Sigma.mk.injEq, add_left_inj] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_iff_eq] at h2
  subst h2
  rfl

/-- Two interlaced `ℕ`-indexed families have the same sum. -/
theorem sum_eq_of_interlaced (a b : ℕ → Cardinal.{u}) (h1 : ∀ k, a k ≤ b k)
    (h2 : ∀ k, b k ≤ a (k + 1)) : Cardinal.sum a = Cardinal.sum b :=
  le_antisymm (sum_le_sum _ _ h1) ((sum_le_sum _ _ h2).trans (sum_shift_le a))

theorem aleph_nat_le_aleph_omega (N : ℕ) : ℵ_ (N : Ordinal.{u}) ≤ ℵ_ ω :=
  aleph_le_aleph.2 (natCast_lt_omega0 N).le

theorem aleph_omega_le_of_forall_nat {c : Cardinal.{u}}
    (h : ∀ N : ℕ, ℵ_ (N : Ordinal.{u}) ≤ c) : ℵ_ ω ≤ c := by
  rw [aleph_limit isSuccLimit_omega0]
  refine ciSup_le' fun a => ?_
  obtain ⟨N, hN⟩ := lt_omega0.1 a.2
  have : (a : Ordinal.{u}) = N := hN
  rw [this]
  exact h N

/-- The cardinality of a disjoint `ℕ`-indexed union is the sum of the cardinalities. -/
theorem mk_iUnion_nat_eq_sum {V : Type u} (t : ℕ → Set V) (h : Pairwise (Disjoint on t)) :
    #(⋃ p, t p) = Cardinal.sum fun p => #(t p) := by
  have := mk_iUnion_eq_sum_mk_lift h
  simpa using this

/-- A countable sum of alephs with unbounded indices below `ω` is `ℵ_ω`. -/
theorem sum_aleph_eq_aleph_omega (e : ℕ → ℕ) (he : ∀ N, N ≤ e N) :
    Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u})) = ℵ_ ω := by
  apply le_antisymm
  · calc Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u}))
        ≤ Cardinal.sum (fun _ : ℕ => (ℵ_ ω : Cardinal.{u})) :=
          sum_le_sum _ _ fun p => aleph_nat_le_aleph_omega (e p)
      _ = ℵ_ ω := by
          rw [sum_const]
          simp only [mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id']
          exact mul_eq_right (aleph0_le_aleph ω) (aleph0_le_aleph ω) aleph0_ne_zero
  · refine aleph_omega_le_of_forall_nat fun N => ?_
    calc ℵ_ (N : Ordinal.{u}) ≤ ℵ_ (e N : Ordinal.{u}) := aleph_le_aleph.2 (by exact_mod_cast he N)
      _ ≤ _ := le_sum _ N

theorem nonempty_of_mk_eq {V : Type u} {s : Set V} {c : Cardinal.{u}} (hs : #s = c)
    (hc : ℵ₀ ≤ c) : s.Nonempty := by
  have : Nonempty s := mk_ne_zero_iff.1 (by rw [hs]; exact (aleph0_pos.trans_le hc).ne')
  exact Set.nonempty_coe_sort.1 this

end

/-! ### Upstream module `Erdos1219/Ramsey.lean` -/

/-!
# Ramsey's theorem for pairs on `ℕ`

We prove the infinite Ramsey theorem for pairs (two colours) on `ℕ` via a non-principal
ultrafilter (`Filter.hyperfilter ℕ`).

Sketch: let `U` be the hyperfilter on `ℕ`.  For each `i` pick the colour `c i` such that
`{j | i < j ∧ g i j = c i} ∈ U`; then pick the colour `δ` with `{i | c i = δ} ∈ U`.
We build a decreasing sequence of sets `S₀ ⊇ S₁ ⊇ …`, all in `U`, all contained in
`{i | c i = δ}`, together with elements `m p ∈ S p`, by
`S (p+1) := S p ∩ {j | m p < j ∧ g (m p) j = δ}`.  Since `m q ∈ S q ⊆ S (p+1)` for `p < q`,
the sequence `m` is strictly increasing and `δ`-homogeneous.
-/

/-- Ramsey's theorem for pairs on `ℕ`: for every colouring `g` of ordered pairs `(p, q)` with
`p < q` (only those values matter), there is a strictly increasing sequence `m` and a colour `δ`
with `g (m p) (m q) = δ` whenever `p < q`. -/
theorem ramsey_nat (g : ℕ → ℕ → Bool) :
    ∃ (m : ℕ → ℕ) (δ : Bool), StrictMono m ∧ ∀ p q, p < q → g (m p) (m q) = δ := by
  classical
  -- the non-principal ultrafilter on `ℕ`
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  -- every final segment `{j | i < j}` belongs to `U`
  have hgt : ∀ i : ℕ, {j | i < j} ∈ U := fun i =>
    Ultrafilter.mem_coe.mp (Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop i))
  -- for each `i` choose the colour `c i` of `U`-almost all `j > i`
  have hc : ∀ i : ℕ, ∃ c : Bool, {j | i < j ∧ g i j = c} ∈ U := by
    intro i
    rcases Ultrafilter.mem_or_compl_mem U {j | g i j = true} with h | h
    · refine ⟨true, ?_⟩
      exact Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr (hgt i)) (Ultrafilter.mem_coe.mpr h))
    · refine ⟨false, ?_⟩
      have h' : {j | g i j = false} ∈ U := by
        refine Ultrafilter.mem_coe.mp
          (Filter.mem_of_superset (Ultrafilter.mem_coe.mpr h) ?_)
        intro j hj
        simpa using hj
      exact Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr (hgt i)) (Ultrafilter.mem_coe.mpr h'))
  choose c hc using hc
  -- choose the colour `δ` taken by `U`-almost all `i`
  have hδ : ∃ δ : Bool, {i | c i = δ} ∈ U := by
    rcases Ultrafilter.mem_or_compl_mem U {i | c i = true} with h | h
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      refine Ultrafilter.mem_coe.mp
        (Filter.mem_of_superset (Ultrafilter.mem_coe.mpr h) ?_)
      intro i hi
      simpa using hi
  obtain ⟨δ, hδ⟩ := hδ
  have key : ∀ i, c i = δ → {j | i < j ∧ g i j = δ} ∈ U := by
    intro i hi
    rw [← hi]
    exact hc i
  -- the type of "good" sets: members of `U` contained in `{i | c i = δ}`
  let T := {S : Set ℕ // S ∈ U ∧ S ⊆ {i | c i = δ}}
  have pick : ∀ S : T, ∃ x, x ∈ S.1 := fun S => Ultrafilter.nonempty_of_mem S.2.1
  choose x hx using pick
  -- one step of the construction
  let step : T → T := fun S =>
    ⟨S.1 ∩ {j | x S < j ∧ g (x S) j = δ},
      Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr S.2.1)
          (Ultrafilter.mem_coe.mpr (key (x S) (S.2.2 (hx S))))),
      fun j hj => S.2.2 hj.1⟩
  let S0 : T := ⟨{i | c i = δ}, hδ, subset_rfl⟩
  let seq : ℕ → T := fun n => Nat.rec S0 (fun _ S => step S) n
  have seq_succ : ∀ n, seq (n + 1) = step (seq n) := fun _ => rfl
  -- the sets are decreasing
  have anti : ∀ p q, p ≤ q → (seq q).1 ⊆ (seq p).1 := by
    intro p q hpq
    induction hpq with
    | refl => exact subset_rfl
    | step _ ih =>
      intro j hj
      apply ih
      rw [seq_succ] at hj
      exact hj.1
  have main : ∀ p q, p < q → x (seq p) < x (seq q) ∧ g (x (seq p)) (x (seq q)) = δ := by
    intro p q hpq
    have h1 : x (seq q) ∈ (seq (p + 1)).1 := anti (p + 1) q hpq (hx (seq q))
    rw [seq_succ] at h1
    exact h1.2
  refine ⟨fun p => x (seq p), δ, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun p => (main p (p + 1) (Nat.lt_succ_self p)).1
  · intro p q hpq
    exact (main p q hpq).2

/-! ### Upstream module `Erdos1219/UnbalancedErdosRado.lean` -/

section
/-!
# The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`

We prove: for every symmetric colouring `f : V → V → Bool`, every infinite cardinal `μ` and
every set `C` of cardinality `(2^μ)⁺`, either `C` contains a `c`-homogeneous set of size
`(2^μ)⁺` or a `!c`-homogeneous set of size `μ⁺`.

The proof is carried out on a well-ordered type `W` of regular cardinality `θ = (2^μ)⁺` whose
order type is the initial ordinal `θ.ord` (concretely `θ.ord.ToType`), and then transported.
-/

open _root_.Cardinal Ordinal _root_.Set

/-! ### Boundedness in well-orders of regular cardinality -/

section WellOrder

variable {X : Type u} [LinearOrder X] [WellFoundedLT X]

/-- In a well-order of regular cardinality `#X` whose order type is the initial ordinal
`(#X).ord`, every subset of cardinality `< #X` is strictly bounded. -/
theorem exists_forall_lt_of_mk_lt (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X)
    {s : Set X} (hs : #s < #X) : ∃ x, ∀ y ∈ s, y < x := by
  rw [← not_isCofinal_iff]
  intro hcof
  have h1 : Order.cof X = #X := by
    rw [← Ordinal.cof_type, ← hX, hreg.cof_ord]
  have h2 := Order.cof_le hcof
  rw [h1] at h2
  exact h2.not_gt hs

theorem exists_gt_of_regular (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X) (x : X) :
    ∃ y, x < y := by
  obtain ⟨y, hy⟩ := exists_forall_lt_of_mk_lt hreg hX (s := {x})
    (by rw [mk_singleton]; exact one_lt_aleph0.trans_le hreg.aleph0_le)
  exact ⟨y, hy x (mem_singleton x)⟩

/-- Well-founded recursion: a sequence `β` indexed by a well-order `I` such that `β ξ` lies
above `h (β η)` for all `η < ξ`, provided all relevant sets are bounded. -/
theorem exists_seq {I W : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder W]
    [WellFoundedLT W] {κ : Cardinal.{u}}
    (hb : ∀ s : Set W, #s < κ → ∃ x, ∀ y ∈ s, y < x) (hI : ∀ ξ : I, #(Iio ξ) < κ)
    (h : W → W) : ∃ β : I → W, ∀ ξ η, η < ξ → h (β η) < β ξ := by
  let F : (ξ : I) → ((η : I) → η < ξ → W) → W := fun ξ IH =>
    Classical.choose (hb (range fun η : Iio ξ => h (IH η η.2)) (mk_range_le.trans_lt (hI ξ)))
  refine ⟨WellFounded.fix wellFounded_lt F, fun ξ η hη => ?_⟩
  rw [WellFounded.fix_eq wellFounded_lt F ξ]
  exact Classical.choose_spec
    (hb (range fun η : Iio ξ => h (WellFounded.fix wellFounded_lt F η))
      (mk_range_le.trans_lt (hI ξ))) _ ⟨⟨η, hη⟩, rfl⟩

end WellOrder

/-! ### The combinatorial core -/

section Main

variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

/-- The `!c`-neighbours of `α` lying below `α`. -/
def nbr (f : W → W → Bool) (c : Bool) (α : W) : Set W := {γ | γ < α ∧ f γ α = !c}

/-- The points joined by colour `!c` to every element of `Z`. -/
def common (f : W → W → Bool) (c : Bool) (Z : Set W) : Set W := {γ | ∀ z ∈ Z, f z γ = !c}

/-- Points of cofinality `> μ`: every subset of the initial segment of size `≤ μ` is bounded
strictly below the point. -/
def bigCof (μ : Cardinal.{u}) : Set W :=
  {α | ∀ Z : Set W, Z ⊆ Iio α → #Z ≤ μ → ∃ β < α, Z ⊆ Iio β}

/-- `α` is *good*: it has big cofinality, and every small `!c`-homogeneous `Z ⊆ nbr f c α`
bounded by some `β < α` admits a `!c`-neighbour of `α` above `β` joined to all of `Z`. -/
def IsGood (f : W → W → Bool) (c : Bool) (μ : Cardinal.{u}) (α : W) : Prop :=
  α ∈ bigCof μ ∧ ∀ Z ⊆ nbr f c α, Homog f (!c) Z → #Z ≤ μ →
    ∀ β < α, Z ⊆ Iio β → ∃ γ ∈ nbr f c α ∩ common f c Z, β ≤ γ

omit [LinearOrder W] [WellFoundedLT W] in
theorem homog_sUnion_of_chain {f : W → W → Bool} {c : Bool} {ch : Set (Set W)}
    (hch : IsChain (· ⊆ ·) ch) (hh : ∀ Z ∈ ch, Homog f c Z) : Homog f c (⋃₀ ch) := by
  intro x hx y hy hxy
  obtain ⟨Z₁, hZ₁, hx⟩ := mem_sUnion.1 hx
  obtain ⟨Z₂, hZ₂, hy⟩ := mem_sUnion.1 hy
  rcases hch.total hZ₁ hZ₂ with h | h
  · exact hh Z₂ hZ₂ x (h hx) y hy hxy
  · exact hh Z₁ hZ₁ x hx y (h hy) hxy

omit [LinearOrder W] [WellFoundedLT W] in
theorem exists_maximal_homog (f : W → W → Bool) (c : Bool) (A : Set W) :
    ∃ Z, Maximal (· ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}) Z := by
  have hchain : ∀ ch ⊆ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, IsChain (· ⊆ ·) ch → ch.Nonempty →
      ∃ ub ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, ∀ s ∈ ch, s ⊆ ub := by
    intro ch hch hchain _
    exact ⟨⋃₀ ch, ⟨sUnion_subset fun Z hZ => (hch hZ).1,
      homog_sUnion_of_chain hchain fun Z hZ => (hch hZ).2⟩, fun Z hZ => subset_sUnion_of_mem hZ⟩
  obtain ⟨Z, -, hZ⟩ := zorn_subset_nonempty {Z : Set W | Z ⊆ A ∧ Homog f c Z} hchain ∅
    ⟨empty_subset _, Homog.empty f c⟩
  exact ⟨Z, hZ⟩

omit [WellFoundedLT W] in
/-- Case 1: a good point yields a `!c`-homogeneous set of size `μ⁺`. -/
theorem good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} {α : W} (hgood : IsGood f c μ α) :
    ∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H := by
  obtain ⟨Z, hZ⟩ := exists_maximal_homog f (!c) (nbr f c α)
  obtain ⟨hZA, hZh⟩ := hZ.1
  have hlt : μ < #Z := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨β, hβα, hZβ⟩ := hgood.1 Z (fun z hz => (hZA hz).1) hle
    obtain ⟨γ, ⟨hγA, hγD⟩, hβγ⟩ := hgood.2 Z hZA hZh hle β hβα hZβ
    have hins : insert γ Z ∈ {Z : Set W | Z ⊆ nbr f c α ∧ Homog f (!c) Z} := by
      refine ⟨insert_subset hγA hZA, ?_⟩
      intro x hx y hy hxy
      rcases mem_insert_iff.1 hx with hxγ | hxZ <;> rcases mem_insert_iff.1 hy with hyγ | hyZ
      · exact absurd (hxγ.trans hyγ.symm) hxy
      · rw [hxγ, hf]; exact hγD y hyZ
      · rw [hyγ]; exact hγD x hxZ
      · exact hZh x hxZ y hyZ hxy
    have heq := hZ.eq_of_subset hins (subset_insert γ Z)
    have hγZ : γ ∈ Z := heq ▸ mem_insert γ Z
    exact absurd (hZβ hγZ) (not_lt.2 hβγ)
  obtain ⟨H, hHZ, hH⟩ := le_mk_iff_exists_subset.1 (Order.succ_le_of_lt hlt)
  exact ⟨H, hH, hZh.mono hHZ⟩

omit [WellFoundedLT W] in
theorem not_good_unfold {f : W → W → Bool} {c : Bool} {μ : Cardinal.{u}} {α : W}
    (hα : α ∈ bigCof μ) (hno : ¬ IsGood f c μ α) :
    ∃ (Z : Set W) (β : W), Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ β < α ∧ Z ⊆ Iio β ∧
      nbr f c α ∩ common f c Z ⊆ Iio β := by
  unfold IsGood at hno
  push Not at hno
  obtain ⟨Z, hZA, hZh, hZμ, β, hβα, hZβ, hγ⟩ := hno hα
  exact ⟨Z, β, hZA, hZh, hZμ, hβα, hZβ, fun γ hγ' => hγ γ hγ'⟩

/-- Claim A (closure-point argument): if `δ` regresses on the points of big cofinality, then
some fibre of `δ` on those points has full cardinality. -/
theorem exists_large_fibre {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (δ : W → W) (hδ : ∀ α ∈ bigCof μ, δ α < α) :
    ∃ δ₀, #W ≤ #{α | α ∈ bigCof μ ∧ δ α = δ₀} := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  by_contra hcon
  push Not at hcon
  -- strict bounds for the (small) fibres
  choose g hg using fun δ₀ => exists_forall_lt_of_mk_lt hreg hord (hcon δ₀)
  -- the closure step `h`
  have hstep : ∀ x : W, #(insert x (g '' Iic x) : Set W) < #W := by
    intro x
    calc #(insert x (g '' Iic x) : Set W) ≤ #(g '' Iic x) + 1 := mk_insert_le
      _ ≤ #(Iic x) + 1 := add_le_add mk_image_le le_rfl
      _ < #W := add_lt_of_lt hℵW (mk_Iic_lt x hord hℵW) (one_lt_aleph0.trans_le hℵW)
  choose h hh using fun x => exists_forall_lt_of_mk_lt hreg hord (hstep x)
  have hxh : ∀ x, x < h x := fun x => hh x x (mem_insert x _)
  have hgh : ∀ x δ', δ' ≤ x → g δ' < h x := fun x δ' hδ' =>
    hh x (g δ') (mem_insert_of_mem x (mem_image_of_mem g hδ'))
  -- the index well-order `I` of cardinality `μ⁺`
  have hI : #((Order.succ μ).ord.ToType) = Order.succ μ := mk_ord_toType _
  have hordI : ord #((Order.succ μ).ord.ToType) = typeLT ((Order.succ μ).ord.ToType) := by
    rw [hI, type_toType]
  have hregI : Cardinal.IsRegular #((Order.succ μ).ord.ToType) := by
    rw [hI]; exact isRegular_succ hμ
  have hμI : μ < #((Order.succ μ).ord.ToType) := by rw [hI]; exact Order.lt_succ μ
  have hIW : #((Order.succ μ).ord.ToType) < #W := by
    rw [hI, hW]
    exact (Order.succ_le_of_lt (cantor μ)).trans_lt (Order.lt_succ _)
  obtain ⟨β, hβ⟩ := exists_seq (I := (Order.succ μ).ord.ToType) (κ := #W)
    (fun s hs => exists_forall_lt_of_mk_lt hreg hord hs)
    (fun ξ => (mk_Iio_lt ξ hordI).trans hIW) h
  have hβmono : ∀ ξ η : (Order.succ μ).ord.ToType, η < ξ → β η < β ξ :=
    fun ξ η hη => (hxh _).trans (hβ ξ η hη)
  -- the least strict upper bound `α₀` of the range of `β`
  have hT : {x : W | ∀ ξ, β ξ < x}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_forall_lt_of_mk_lt hreg hord (s := range β)
      (mk_range_le.trans_lt hIW)
    exact ⟨x, fun ξ => hx _ (mem_range_self ξ)⟩
  obtain ⟨α₀, hα₀T, hbelow⟩ : ∃ α₀ : W, (∀ ξ, β ξ < α₀) ∧ ∀ y, y < α₀ → ∃ ξ, y ≤ β ξ := by
    refine ⟨(wellFounded_lt (α := W)).min _ hT, (wellFounded_lt (α := W)).min_mem _ hT, ?_⟩
    intro y hy
    by_contra hcon'
    push Not at hcon'
    exact (wellFounded_lt (α := W)).not_lt_min {x : W | ∀ ξ, β ξ < x} (x := y) hcon' hy
  -- `α₀` has big cofinality
  have hα₀S : α₀ ∈ bigCof μ := by
    intro Z hZ hZμ
    choose ξ hξ using fun z : Z => hbelow z (hZ z.2)
    obtain ⟨ξ', hξ'⟩ := exists_forall_lt_of_mk_lt hregI hordI (s := range ξ)
      (mk_range_le.trans_lt (hZμ.trans_lt hμI))
    refine ⟨β ξ', hα₀T ξ', fun z hz => ?_⟩
    exact (hξ ⟨z, hz⟩).trans_lt (hβmono _ _ (hξ' _ (mem_range_self _)))
  -- but `α₀` lies in the fibre of `δ α₀`, which is bounded below `α₀`
  have h1 : α₀ < g (δ α₀) := hg (δ α₀) α₀ ⟨hα₀S, rfl⟩
  obtain ⟨ξ, hξ⟩ := hbelow _ (hδ α₀ hα₀S)
  obtain ⟨ξ', hξξ'⟩ := exists_gt_of_regular hregI hordI ξ
  have h2 : g (δ α₀) < β ξ' := (hgh _ _ hξ).trans (hβ ξ' ξ hξξ')
  exact lt_irrefl α₀ (h1.trans (h2.trans (hα₀T ξ')))

/-- Case 2: if no point is good, there is a `c`-homogeneous set of full cardinality. -/
theorem no_good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (hno : ∀ α, ¬ IsGood f c μ α) : ∃ H : Set W, #H = #W ∧ Homog f c H := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  have hchoice : ∀ α : W, ∃ (Z : Set W) (δ : W), α ∈ bigCof μ →
      (Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ δ < α ∧ Z ⊆ Iio δ ∧
        nbr f c α ∩ common f c Z ⊆ Iio δ) := by
    intro α
    by_cases hα : α ∈ bigCof μ
    · obtain ⟨Z, δ, hZδ⟩ := not_good_unfold hα (hno α)
      exact ⟨Z, δ, fun _ => hZδ⟩
    · exact ⟨∅, α, fun h => absurd h hα⟩
  choose Z δ hZδ using hchoice
  obtain ⟨δ₀, hδ₀⟩ := exists_large_fibre hμ hW hord δ fun α hα => (hZδ α hα).2.2.2.1
  -- Claim B: pigeonhole on the map `α ↦ Z α`
  have hTcard : #{t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} < (#W).ord.cof := by
    rw [hreg.cof_ord]
    refine (mk_bounded_subset_le (Iio δ₀) μ).trans_lt ?_
    have hIio : #(Iio δ₀) ≤ 2 ^ μ := by
      rw [← Order.lt_succ_iff, ← hW]
      exact mk_Iio_lt δ₀ hord
    calc max #(Iio δ₀) ℵ₀ ^ μ ≤ (2 ^ μ) ^ μ := power_le_power_right (max_le hIio h2μ)
      _ = 2 ^ μ := by rw [← power_mul, mul_eq_self hμ]
      _ < #W := by rw [hW]; exact Order.lt_succ _
  let φ : {α | α ∈ bigCof μ ∧ δ α = δ₀} → {t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} := fun α =>
    ⟨Z α, by
      have h := hZδ α.1 α.2.1
      refine ⟨h.2.2.2.2.1.trans ?_, h.2.2.1⟩
      rw [α.2.2]⟩
  obtain ⟨Z₀, t, htF, htcard, hφ⟩ := infinite_pigeonhole_set φ #W hδ₀ hℵW hTcard
  have htZ : ∀ x ∈ t, Z x = Z₀.1 := fun x hx => congrArg Subtype.val (hφ hx)
  have htW : #t = #W := le_antisymm (mk_set_le t) htcard
  -- Claim C: remove the points `≤ δ₀`
  refine ⟨t \ Iic δ₀, ?_, ?_⟩
  · have h1 : t.Infinite := infinite_coe_iff.1 (infinite_iff.2 (hℵW.trans htcard))
    have h2 : #(Iic δ₀) < #t := by rw [htW]; exact mk_Iic_lt δ₀ hord hℵW
    rw [mk_sdiff_eq_left h1 h2, htW]
  · have hbool : ∀ b d : Bool, ¬ b = d → b = !d := by decide
    have key : ∀ a ∈ t \ Iic δ₀, ∀ a' ∈ t \ Iic δ₀, a < a' → f a a' = c := by
      intro a ha a' ha' hlt
      have haF := htF ha.1
      have ha'F := htF ha'.1
      have hZa := hZδ a haF.1
      have hZa' := hZδ a' ha'F.1
      have haD : a ∈ common f c (Z a') := by
        intro z hz
        rw [htZ a' ha'.1, ← htZ a ha.1] at hz
        exact (hZa.1 hz).2
      by_contra hne
      have hmem : a ∈ nbr f c a' ∩ common f c (Z a') := ⟨⟨hlt, hbool _ _ hne⟩, haD⟩
      have hlt' := hZa'.2.2.2.2.2 hmem
      rw [ha'F.2] at hlt'
      exact ha.2 (le_of_lt hlt')
    intro a ha a' ha' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a ha a' ha' h
    · rw [hf]; exact key a' ha' a ha h

/-- The theorem on a well-ordered type of cardinality `(2^μ)⁺` and order type `(2^μ)⁺.ord`. -/
theorem erdosRado_unbalanced_wo {f : W → W → Bool} (hf : ∀ x y, f x y = f y x)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (c : Bool) :
    (∃ H : Set W, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H) := by
  by_cases hg : ∃ α, IsGood f c μ α
  · obtain ⟨α, hα⟩ := hg
    exact Or.inr (good_case hf hα)
  · push Not at hg
    obtain ⟨H, hH, hHc⟩ := no_good_case hf hμ hW hord hg
    exact Or.inl ⟨H, hH.trans hW, hHc⟩

end Main

/-! ### The theorem on an arbitrary type -/

/-- The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`, stated for both colours `c`. -/
theorem erdosRado_unbalanced {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (C : Set V) (hC : #C = Order.succ (2 ^ μ)) (c : Bool) :
    (∃ H ⊆ C, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H ⊆ C, #H = Order.succ μ ∧ Homog f (!c) H) := by
  have hW : #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) = Order.succ (2 ^ μ) :=
    mk_ord_toType _
  have hord : ord #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) =
      typeLT ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) := by
    rw [hW, type_toType]
  obtain ⟨e⟩ : Nonempty (C ≃ (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) :=
    Cardinal.eq.1 (hC.trans hW.symm)
  let g : (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType → V := fun x => (e.symm x : V)
  have hg : Function.Injective g := fun x y hxy =>
    e.symm.injective (Subtype.val_injective hxy)
  have hf' : ∀ x y, f (g x) (g y) = f (g y) (g x) := fun x y => hf _ _
  have transport : ∀ (d : Bool) (H : Set ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType)),
      Homog (fun x y => f (g x) (g y)) d H →
        g '' H ⊆ C ∧ #(g '' H) = #H ∧ Homog f d (g '' H) := by
    intro d H hH
    refine ⟨?_, mk_image_eq hg, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (e.symm x).2
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hH x hx y hy fun h => hxy (congrArg g h)
  rcases erdosRado_unbalanced_wo hf' hμ hW hord c with ⟨H, hH, hHc⟩ | ⟨H, hH, hHc⟩
  · obtain ⟨h1, h2, h3⟩ := transport c H hHc
    exact Or.inl ⟨g '' H, h1, h2.trans hH, h3⟩
  · obtain ⟨h1, h2, h3⟩ := transport (!c) H hHc
    exact Or.inr ⟨g '' H, h1, h2.trans hH, h3⟩

end

/-! ### Upstream module `Erdos1219/Canonization.lean` -/

section
/-!
# The canonization argument (Shelah, Notes on partition calculus, §1)

We formalize the proof of Shelah's Theorem 1.2 (special case: `λ = ℵ_ω`), following the
Canonization Lemma 1.1 of that paper.  See `docs/PROOF.md` for the mathematical proof.

The colouring is a symmetric `f : V → V → Bool`, the vertex set `V` is (essentially) the disjoint
union of blocks `A k` with `#(A k) = lam k := (2 ^ ℵ_{n k})⁺`.  Assuming that there is no
homogeneous set of size `ℵ_ω` at all (`hno`), every block contains, inside every subset of full
size, homogeneous sets of both colours of size `μ k := ℵ_{n k}` (unbalanced Erdős–Rado).  A
"guide" `guide k ∈ A k` avoiding the small set `bad k` is chosen in each block; then blocks
`B k = (B k).1 ∪ (B k).2` (a `false`-homogeneous and a `true`-homogeneous part, each of size
`μ k`) are chosen inductively inside the class of the guide over the earlier blocks, all with the
same type over the guides.  This makes the colouring canonical across blocks, so that Ramsey's
theorem on `ℕ` produces the required homogeneous set of size `ℵ_ω`, a contradiction.
-/

open _root_.Cardinal Ordinal _root_.Function

/-- The data of the argument: a symmetric colouring on `V`, the sequence `n`, blocks `A k` of
size `(2 ^ ℵ_{n k})⁺`, and the assumption that there is no homogeneous set of size `ℵ_ω`. -/
structure Ctx (V : Type u) where
  f : V → V → Bool
  hf : ∀ x y, f x y = f y x
  n : ℕ → ℕ
  hn : StrictMono n
  hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)
  h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)
  A : ℕ → Set V
  hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))
  hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  hno : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω

namespace Ctx

variable {V : Type u} (S : Ctx V)

/-! ### Cardinal bookkeeping -/

/-- `μ k = ℵ_{n k}`. -/
noncomputable def μ (k : ℕ) : Cardinal.{u} := ℵ_ (S.n k : Ordinal.{u})

/-- `lam k = (2 ^ μ k)⁺`, the size of the `k`-th block. -/
noncomputable def lam (k : ℕ) : Cardinal.{u} := Order.succ (2 ^ S.μ k)

theorem mk_A (k : ℕ) : #(S.A k) = S.lam k := S.hA k

theorem aleph0_le_μ (k : ℕ) : ℵ₀ ≤ S.μ k := aleph0_le_aleph _

theorem μ_mono {i k : ℕ} (h : i ≤ k) : S.μ i ≤ S.μ k :=
  aleph_le_aleph.2 (by exact_mod_cast S.hn.monotone h)

theorem two_pow_μ_lt {i k : ℕ} (h : i < k) : (2 : Cardinal.{u}) ^ S.μ i < 2 ^ S.μ k := S.hpow h

theorem two_pow_μ_le {i k : ℕ} (h : i ≤ k) : (2 : Cardinal.{u}) ^ S.μ i ≤ 2 ^ S.μ k :=
  S.hpow.monotone h

theorem aleph0_le_two_pow_μ (k : ℕ) : ℵ₀ ≤ (2 : Cardinal.{u}) ^ S.μ k :=
  aleph0_le_two_pow (S.aleph0_le_μ k)

theorem lam_isRegular (k : ℕ) : (S.lam k).IsRegular := isRegular_succ (S.aleph0_le_two_pow_μ k)

theorem two_pow_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ S.μ k < S.lam k := Order.lt_succ _

theorem lam_le_two_pow_succ (k : ℕ) : S.lam k ≤ 2 ^ S.μ (k + 1) :=
  Order.succ_le_of_lt (S.two_pow_μ_lt (Nat.lt_succ_self k))

theorem aleph_omega_lt_two_pow (k : ℕ) : ℵ_ ω < (2 : Cardinal.{u}) ^ S.μ k :=
  S.h0.trans_le (S.two_pow_μ_le (Nat.zero_le k))

theorem aleph_omega_lt_lam (k : ℕ) : ℵ_ ω < S.lam k :=
  (S.aleph_omega_lt_two_pow k).trans (S.two_pow_lt_lam k)

theorem two_pow_aleph0_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ ℵ₀ < S.lam k :=
  (power_le_power_left two_ne_zero (S.aleph0_le_μ k)).trans_lt (S.two_pow_lt_lam k)

/-! ### Homogeneous sets of both colours inside every large subset of a block -/

/-- There is no homogeneous set of size `lam k` (it would contain one of size `ℵ_ω`). -/
theorem noBig (k : ℕ) (c : Bool) (H : Set V) (hH : Homog S.f c H) : #H ≠ S.lam k := by
  intro hHk
  obtain ⟨H', hH'sub, hH'⟩ :=
    le_mk_iff_exists_subset.1 ((S.aleph_omega_lt_lam k).le.trans_eq hHk.symm)
  exact S.hno c H' (hH.mono hH'sub) hH'

/-- Every subset of full size of a block contains homogeneous sets of both colours of size
`μ k` (unbalanced Erdős–Rado). -/
theorem exists_homog_two (k : ℕ) (C : Set V) (hC : #C = S.lam k) :
    ∃ B0 B1 : Set V, B0 ⊆ C ∧ B1 ⊆ C ∧ #B0 = S.μ k ∧ #B1 = S.μ k ∧
      Homog S.f false B0 ∧ Homog S.f true B1 := by
  have h0 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC true
  have h1 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC false
  rcases h0 with ⟨H, -, hH, hom⟩ | ⟨H0, hH0C, hH0, hom0⟩
  · exact absurd hH (S.noBig k true H hom)
  rcases h1 with ⟨H, -, hH, hom⟩ | ⟨H1, hH1C, hH1, hom1⟩
  · exact absurd hH (S.noBig k false H hom)
  obtain ⟨B0, hB0, hB0c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH0.symm)
  obtain ⟨B1, hB1, hB1c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH1.symm)
  exact ⟨B0, B1, hB0.trans hH0C, hB1.trans hH1C, hB0c, hB1c, hom0.mono hB0, hom1.mono hB1⟩

/-! ### The union of the earlier blocks -/

/-- `U k = A 0 ∪ ... ∪ A (k-1)`. -/
noncomputable def U (S : Ctx V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => U S k ∪ S.A k

theorem mem_U {v : V} {k : ℕ} : v ∈ S.U k ↔ ∃ i, i < k ∧ v ∈ S.A i := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    simp only [U, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hv⟩
      · exact Or.inr hv

theorem A_subset_U {i k : ℕ} (h : i < k) : S.A i ⊆ S.U k := fun _ hv => S.mem_U.2 ⟨i, h, hv⟩

theorem mk_U_le (k : ℕ) : #(S.U k) ≤ 2 ^ S.μ k := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    calc #(S.U (k + 1)) = #(S.U k ∪ S.A k : Set V) := by rw [U]
      _ ≤ #(S.U k) + #(S.A k) := mk_union_le _ _
      _ ≤ 2 ^ S.μ (k + 1) + 2 ^ S.μ (k + 1) :=
          add_le_add (ih.trans (S.two_pow_μ_le (Nat.le_succ k)))
            (by rw [S.mk_A]; exact S.lam_le_two_pow_succ k)
      _ = 2 ^ S.μ (k + 1) := add_eq_self (S.aleph0_le_two_pow_μ _)

/-! ### Classes, bad points and guides -/

/-- The class of `a` over `B` inside the block `A k`: the points of `A k` with the same
colours towards `B` as `a`. -/
def cls (k : ℕ) (a : V) (B : Set V) : Set V := {a' ∈ S.A k | ∀ b ∈ B, S.f a' b = S.f a b}

theorem cls_subset_A (k : ℕ) (a : V) (B : Set V) : S.cls k a B ⊆ S.A k := fun _ h => h.1

/-- The bad points of `A k`: those having a small class over some small subset of `U k`. -/
def bad (k : ℕ) : Set V :=
  {a ∈ S.A k | ∃ B : Set V, B ⊆ S.U k ∧ #B ≤ S.μ k ∧ #(S.cls k a B) < S.lam k}

/-- The type of `a` over `B`. -/
def tp (a : V) (B : Set V) : Set (↥B) := {b | S.f a b = true}

theorem cls_eq_fib (k : ℕ) (a : V) (B : Set V) :
    S.cls k a B = {a' ∈ S.A k | S.tp a' B = S.tp a B} := by
  ext a'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext b
    show S.f a' b = true ↔ S.f a b = true
    rw [h2 b b.2]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun b hb => ?_⟩
    have := Set.ext_iff.1 h2 ⟨b, hb⟩
    exact Bool.eq_iff_iff.2 this

theorem mk_small_lt (k : ℕ) (B : Set V) (hB : #B ≤ S.μ k) :
    #({a ∈ S.A k | #(S.cls k a B) < S.lam k} : Set V) < S.lam k := by
  have hsub : {a ∈ S.A k | #(S.cls k a B) < S.lam k} ⊆
      ⋃ (t : {t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}),
        {a ∈ S.A k | S.tp a B = t.1} := by
    rintro a ⟨ha, hlt⟩
    rw [S.cls_eq_fib] at hlt
    exact Set.mem_iUnion.2 ⟨⟨S.tp a B, hlt⟩, ha, rfl⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun t => t.2)
  calc #{t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}
      ≤ #(Set (↥B)) := mk_subtype_le _
    _ = 2 ^ #B := mk_set
    _ ≤ 2 ^ S.μ k := power_le_power_left two_ne_zero hB
    _ < S.lam k := S.two_pow_lt_lam k

theorem mk_bad_lt (k : ℕ) : #(S.bad k) < S.lam k := by
  have hsub : S.bad k ⊆ ⋃ (B : {B : Set V // B ⊆ S.U k ∧ #B ≤ S.μ k}),
      {a ∈ S.A k | #(S.cls k a B.1) < S.lam k} := by
    rintro a ⟨ha, B, hBU, hBμ, hlt⟩
    exact Set.mem_iUnion.2 ⟨⟨B, hBU, hBμ⟩, ha, hlt⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun B => S.mk_small_lt k B.1 B.2.2)
  exact (mk_bounded_subsets_le (S.U k) (S.aleph0_le_μ k) (S.mk_U_le k)).trans_lt
    (S.two_pow_lt_lam k)

theorem exists_guide (k : ℕ) : ∃ a, a ∈ S.A k ∧ a ∉ S.bad k := by
  by_contra h
  have hsub : S.A k ⊆ S.bad k := fun a ha => by
    by_contra hb
    exact h ⟨a, ha, hb⟩
  have := (mk_le_mk_of_subset hsub).trans_lt (S.mk_bad_lt k)
  rw [S.mk_A] at this
  exact lt_irrefl _ this

/-- The guide of block `k`: a point of `A k` that is not bad. -/
noncomputable def guide (k : ℕ) : V := (S.exists_guide k).choose

theorem guide_mem (k : ℕ) : S.guide k ∈ S.A k := (S.exists_guide k).choose_spec.1

theorem guide_not_bad (k : ℕ) : S.guide k ∉ S.bad k := (S.exists_guide k).choose_spec.2

theorem mk_cls_guide (k : ℕ) (B : Set V) (hBU : B ⊆ S.U k) (hBμ : #B ≤ S.μ k) :
    #(S.cls k (S.guide k) B) = S.lam k := by
  apply le_antisymm
  · exact (mk_le_mk_of_subset (S.cls_subset_A k _ B)).trans_eq (S.mk_A k)
  · by_contra h
    exact S.guide_not_bad k ⟨S.guide_mem k, B, hBU, hBμ, lt_of_not_ge h⟩

/-! ### The blocks -/

/-- The basic requirement on the `k`-th pair of blocks: both parts lie in `A k` and the union
has size at most `μ k`. -/
structure Basic (k : ℕ) (p : Set V × Set V) : Prop where
  sub : p.1 ∪ p.2 ⊆ S.A k
  mk_le : #(p.1 ∪ p.2 : Set V) ≤ S.μ k

/-- The union of the earlier blocks `prev i` (`i < k`). -/
noncomputable def prevU (S : Ctx V) : (k : ℕ) → (∀ i, i < k → Set V × Set V) → Set V
  | 0, _ => ∅
  | k + 1, prev =>
      prevU S k (fun i h => prev i (Nat.lt_succ_of_lt h)) ∪
        ((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2)

theorem mem_prevU {k : ℕ} {prev : ∀ i, i < k → Set V × Set V} {v : V} :
    v ∈ S.prevU k prev ↔ ∃ i, ∃ h : i < k, v ∈ (prev i h).1 ∪ (prev i h).2 := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    simp only [prevU, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · exact Or.inl ⟨i, hi', hv⟩
      · exact Or.inr hv

theorem mk_prevU_le {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : #(S.prevU k prev) ≤ S.μ k := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    calc #(S.prevU (k + 1) prev)
        ≤ #(S.prevU k (fun i h => prev i (Nat.lt_succ_of_lt h))) +
            #((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2 : Set V) :=
          mk_union_le _ _
      _ ≤ S.μ (k + 1) + S.μ (k + 1) :=
          add_le_add ((ih (fun i h => hprev i _)).trans (S.μ_mono (Nat.le_succ k)))
            ((hprev k _).mk_le.trans (S.μ_mono (Nat.le_succ k)))
      _ = S.μ (k + 1) := add_eq_self (S.aleph0_le_μ _)

theorem prevU_subset_U {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : S.prevU k prev ⊆ S.U k := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := S.mem_prevU.1 hv
  exact S.A_subset_U hi ((hprev i hi).sub hvi)

/-- The properties of the `k`-th pair of blocks, relative to the earlier ones. -/
structure Good (k : ℕ) (prev : ∀ i, i < k → Set V × Set V) (p : Set V × Set V) : Prop where
  sub1 : p.1 ⊆ S.A k
  sub2 : p.2 ⊆ S.A k
  mk1 : #p.1 = S.μ k
  mk2 : #p.2 = S.μ k
  hom1 : Homog S.f false p.1
  hom2 : Homog S.f true p.2
  cls : ∀ a ∈ p.1 ∪ p.2, ∀ b ∈ S.prevU k prev, S.f a b = S.f (S.guide k) b
  same : ∀ a ∈ p.1 ∪ p.2, ∀ a' ∈ p.1 ∪ p.2, ∀ j, S.f a (S.guide j) = S.f a' (S.guide j)

/-- The type of a point over the guides. -/
def gtp (a : V) : Set (ULift.{u} ℕ) := {j | S.f a (S.guide j.down) = true}

theorem mk_set_uLift_nat_lt_lam (k : ℕ) : #(Set (ULift.{u} ℕ)) < S.lam k := by
  rw [mk_set, mk_uLift, mk_nat, Cardinal.lift_aleph0]
  exact S.two_pow_aleph0_lt_lam k

theorem exists_blocks (k : ℕ) (prev : ∀ i, i < k → Set V × Set V)
    (hprev : ∀ i h, S.Basic i (prev i h)) : ∃ p, S.Good k prev p ∧ S.Basic k p := by
  have hB1c : #(S.cls k (S.guide k) (S.prevU k prev)) = S.lam k :=
    S.mk_cls_guide k _ (S.prevU_subset_U hprev) (S.mk_prevU_le hprev)
  obtain ⟨t, ht⟩ := exists_fiber_eq_of_isRegular (S.lam_isRegular k) _ hB1c S.gtp
    (S.mk_set_uLift_nat_lt_lam k)
  obtain ⟨B0, B1, hB0, hB1, hB0c, hB1c, hom0, hom1⟩ := S.exists_homog_two k _ ht
  have hB0A : B0 ⊆ S.A k := fun a ha => (hB0 ha).1.1
  have hB1A : B1 ⊆ S.A k := fun a ha => (hB1 ha).1.1
  have hcls : ∀ a ∈ B0 ∪ B1, a ∈ S.cls k (S.guide k) (S.prevU k prev) := by
    rintro a (ha | ha)
    · exact (hB0 ha).1
    · exact (hB1 ha).1
  have htp : ∀ a ∈ B0 ∪ B1, S.gtp a = t := by
    rintro a (ha | ha)
    · exact (hB0 ha).2
    · exact (hB1 ha).2
  refine ⟨(B0, B1), ⟨hB0A, hB1A, hB0c, hB1c, hom0, hom1, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a ha b hb
    exact (hcls a ha).2 b hb
  · intro a ha a' ha' j
    have h := (htp a ha).trans (htp a' ha').symm
    have h' : S.f a (S.guide j) = true ↔ S.f a' (S.guide j) = true := Set.ext_iff.1 h ⟨j⟩
    exact Bool.eq_iff_iff.2 h'
  · exact Set.union_subset hB0A hB1A
  · calc #(B0 ∪ B1 : Set V) ≤ #B0 + #B1 := mk_union_le _ _
      _ = S.μ k + S.μ k := by rw [hB0c, hB1c]
      _ = S.μ k := add_eq_self (S.aleph0_le_μ k)

/-- The blocks, defined by strong recursion. -/
noncomputable def blocks (S : Ctx V) : (k : ℕ) → {p : Set V × Set V // S.Basic k p}
  | k =>
    ⟨(S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose,
      (S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose_spec.2⟩
termination_by k => k

/-- The `k`-th pair of blocks. -/
noncomputable def B (k : ℕ) : Set V × Set V := (S.blocks k).1

theorem B_basic (k : ℕ) : S.Basic k (S.B k) := (S.blocks k).2

theorem blocks_good (k : ℕ) : S.Good k (fun i _ => S.B i) (S.B k) := by
  unfold B
  rw [blocks]
  exact (S.exists_blocks k (fun i _ => (S.blocks i).1)
    (fun i _ => (S.blocks i).2)).choose_spec.1

/-- The union of the two parts of the `k`-th block. -/
noncomputable def Bu (k : ℕ) : Set V := (S.B k).1 ∪ (S.B k).2

theorem Bu_subset_A (k : ℕ) : S.Bu k ⊆ S.A k := (S.B_basic k).sub

theorem mem_prevU_B {i j : ℕ} (hij : i < j) {a : V} (ha : a ∈ S.Bu i) :
    a ∈ S.prevU j (fun i _ => S.B i) :=
  S.mem_prevU.2 ⟨i, hij, ha⟩

/-! ### Canonicity -/

theorem canonical {i j : ℕ} (hij : i < j) {a a' b : V} (ha : a ∈ S.Bu i) (ha' : a' ∈ S.Bu i)
    (hb : b ∈ S.Bu j) : S.f a b = S.f a' b := by
  have hj := (S.blocks_good j).cls
  have hi := (S.blocks_good i).same
  calc S.f a b = S.f b a := S.hf a b
    _ = S.f (S.guide j) a := hj b hb a (S.mem_prevU_B hij ha)
    _ = S.f a (S.guide j) := S.hf _ _
    _ = S.f a' (S.guide j) := hi a ha a' ha' j
    _ = S.f (S.guide j) a' := S.hf _ _
    _ = S.f b a' := (hj b hb a' (S.mem_prevU_B hij ha')).symm
    _ = S.f a' b := S.hf _ _

/-- A chosen point of the `false`-part of the `i`-th block. -/
noncomputable def pick (i : ℕ) : V :=
  (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose

theorem pick_mem (i : ℕ) : S.pick i ∈ S.Bu i :=
  Or.inl (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose_spec

/-- The colour between the `i`-th and `j`-th blocks (`i < j`). -/
noncomputable def g (i j : ℕ) : Bool := S.f (S.pick i) (S.guide j)

theorem cross {i j : ℕ} (hij : i < j) {a b : V} (ha : a ∈ S.Bu i) (hb : b ∈ S.Bu j) :
    S.f a b = S.g i j := by
  have hj := (S.blocks_good j).cls
  calc S.f a b = S.f (S.pick i) b := S.canonical hij ha (S.pick_mem i) hb
    _ = S.f b (S.pick i) := S.hf _ _
    _ = S.f (S.guide j) (S.pick i) := hj b hb _ (S.mem_prevU_B hij (S.pick_mem i))
    _ = S.f (S.pick i) (S.guide j) := S.hf _ _

/-! ### The homogeneous set -/

/-- The `δ`-homogeneous part of the `k`-th block. -/
noncomputable def part (δ : Bool) (k : ℕ) : Set V := bif δ then (S.B k).2 else (S.B k).1

theorem part_subset_Bu (δ : Bool) (k : ℕ) : S.part δ k ⊆ S.Bu k := by
  cases δ
  · exact fun a ha => Or.inl ha
  · exact fun a ha => Or.inr ha

theorem part_homog (δ : Bool) (k : ℕ) : Homog S.f δ (S.part δ k) := by
  cases δ
  · exact (S.blocks_good k).hom1
  · exact (S.blocks_good k).hom2

theorem mk_part (δ : Bool) (k : ℕ) : #(S.part δ k) = S.μ k := by
  cases δ
  · exact (S.blocks_good k).mk1
  · exact (S.blocks_good k).mk2

theorem exists_homog : ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog S.f c H := by
  obtain ⟨m, δ, hm, hδ⟩ := ramsey_nat S.g
  refine ⟨δ, ⋃ p, S.part δ (m p), ?_, ?_⟩
  · have hdisj' : Pairwise (Disjoint on fun p => S.part δ (m p)) := by
      intro p q hpq
      exact Set.disjoint_of_subset (S.part_subset_Bu δ (m p)) (S.part_subset_Bu δ (m q))
        ((S.hdisj _ _ (hm.injective.ne hpq)).mono (S.Bu_subset_A _) (S.Bu_subset_A _))
    rw [mk_iUnion_nat_eq_sum _ hdisj']
    simp only [S.mk_part]
    exact sum_aleph_eq_aleph_omega (fun p => S.n (m p))
      (fun N => (hm.id_le N).trans (S.hn.id_le _))
  · intro x hx y hy hxy
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
    obtain ⟨q, hyq⟩ := Set.mem_iUnion.1 hy
    rcases lt_trichotomy p q with h | rfl | h
    · rw [S.cross (hm h) (S.part_subset_Bu _ _ hxp) (S.part_subset_Bu _ _ hyq)]
      exact hδ p q h
    · exact S.part_homog δ (m p) x hxp y hyq hxy
    · rw [S.hf, S.cross (hm h) (S.part_subset_Bu _ _ hyq) (S.part_subset_Bu _ _ hxp)]
      exact hδ q p h

end Ctx

/-! ### The core theorem -/

/-- The core theorem: for a symmetric pair colouring of a set of size `Σ_k 2^{ℵ_{n_k}}`, there
is a homogeneous set of size `ℵ_ω`. -/
theorem core {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0))
    (hV : #V = Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) :
    ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog f c H := by
  by_contra hno
  have hsum : #V = #(Σ k : ℕ, (Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))).out) := by
    rw [hV]
    exact sum_eq_of_interlaced _ _ (fun k => Order.le_succ _)
      (fun k => Order.succ_le_of_lt (hpow (Nat.lt_succ_self k)))
  obtain ⟨e⟩ := Cardinal.eq.1 hsum
  let A : ℕ → Set V := fun k => e.symm '' Set.range (Sigma.mk k)
  have hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k)) := by
    intro k
    simp only [A]
    rw [mk_image_eq e.symm.injective, mk_range_eq _ sigma_mk_injective, mk_out]
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    simp only [A]
    rw [Set.disjoint_image_iff e.symm.injective]
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (Sigma.mk.inj_iff.1 hb).1.symm
  have hno' : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω :=
    fun c H hH hc => hno ⟨c, H, hc, hH⟩
  let S : Ctx V := ⟨f, hf, n, hn, hpow, h0, A, hA, hdisj, hno'⟩
  obtain ⟨c, H, h1, h2⟩ := S.exists_homog
  exact hno ⟨c, H, h1, h2⟩

end

/-! ### Upstream module `Erdos1219/Main.lean` -/

section
/-!
# Erdős problem #1219: the statement on colourings of `2`-element finsets
-/

open _root_.Cardinal Ordinal

/-- **Erdős problem #1219** (Erdős–Hajnal–Rado; proved by Shelah).  Let `(n_k)` be an increasing
sequence of natural numbers such that `2 ^ ℵ_{n_k}` is strictly increasing and
`2 ^ ℵ_{n_0} > ℵ_ω`.  Then `Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`. -/
theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by
  intro A hA col
  obtain ⟨c, H, hH, hom⟩ :=
    core (ofFinsetColouring col) (ofFinsetColouring_symm col) n hn hpow h0 hA
  refine ⟨c, H, hH, ?_⟩
  intro s hs hsH
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
  have hx : x ∈ H := hsH (by simp)
  have hy : y ∈ H := hsH (by simp)
  have := hom x hx y hy hxy
  rw [ofFinsetColouring_apply col hxy] at this
  exact this

end

#print axioms erdos_1219
-- 'Erdos1219.erdos_1219' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1219
