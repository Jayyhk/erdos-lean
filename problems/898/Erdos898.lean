/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9bfd1506-a97b-4882-a9c0-69353ce590be

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma dist_projections_ge_projection_on_side {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    let Pb : V
-/

import Mathlib

namespace Erdos898

open EuclideanGeometry Metric RealInnerProductSpace

set_option maxHeartbeats 1000000

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable [hV : Fact (Module.finrank ℝ V = 2)]

/-- Distance from a point to a line defined by two points. -/
def dist_to_line (P A B : V) : ℝ :=
  dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P)

/- Pedal triangle property placeholder. -/
noncomputable section AristotleLemmas

/-
An algebraic identity for 2D inner product spaces: the squared norm of the difference of projections of a vector `w` onto two unit vectors `u` and `v` is `‖w‖^2 * (1 - ⟨u, v⟩^2)`.
-/
lemma norm_inner_smul_sub_inner_smul_sq_of_dim_two
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [hV : Fact (Module.finrank ℝ V = 2)]
    (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℝ w v • v - inner ℝ w u • u‖^2 = ‖w‖^2 * (1 - (inner ℝ u v)^2) := by
      simp +decide [ @norm_sub_sq ℝ ];
      simp_all +decide [ norm_smul, inner_smul_left, inner_smul_right ] ; ring_nf;
      -- By the properties of the inner product and the fact that $u$ and $v$ are unit vectors, we can simplify the expression.
      have h_inner : ⟪w, v⟫ ^ 2 + ⟪w, u⟫ ^ 2 - 2 * ⟪w, u⟫ * ⟪w, v⟫ * ⟪u, v⟫ = ‖w‖ ^ 2 * (1 - ⟪u, v⟫ ^ 2) := by
        have h_basis : ∃ (e1 e2 : V), ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ ⟪e1, e2⟫ = 0 ∧ ∀ w : V, ∃ (a b : ℝ), w = a • e1 + b • e2 := by
          -- Since $V$ is a 2-dimensional inner product space, we can choose an orthonormal basis $\{e_1, e_2\}$.
          obtain ⟨e1, e2, he1, he2, h_orth⟩ : ∃ e1 e2 : V, ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ ⟪e1, e2⟫ = 0 ∧ Submodule.span ℝ {e1, e2} = ⊤ := by
            have h_basis : ∃ (b : OrthonormalBasis (Fin 2) ℝ V), True := by
              simp +zetaDelta at *;
              refine' ⟨ _ ⟩;
              convert ( stdOrthonormalBasis ℝ V );
              exact hV.1.symm;
            obtain ⟨ b, - ⟩ := h_basis; use b 0, b 1; simp_all +decide ;
            have := b.sum_repr;
            refine' eq_top_iff.mpr fun x hx => _;
            exact this x ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( by fin_cases i <;> simp +decide ) );
          refine' ⟨ e1, e2, he1, he2, h_orth.1, fun w => _ ⟩;
          have := h_orth.2.ge ( Submodule.mem_top : w ∈ ⊤ ) ; rw [ Submodule.mem_span_pair ] at this; tauto;
        obtain ⟨ e1, e2, he1, he2, he1e2, hw ⟩ := h_basis;
        -- By the properties of the inner product and the fact that $e1$ and $e2$ are orthonormal, we can express $u$ and $v$ in terms of $e1$ and $e2$.
        obtain ⟨a1, a2, ha⟩ : ∃ a1 a2 : ℝ, u = a1 • e1 + a2 • e2 := hw u
        obtain ⟨b1, b2, hb⟩ : ∃ b1 b2 : ℝ, v = b1 • e1 + b2 • e2 := hw v
        obtain ⟨c1, c2, hc⟩ : ∃ c1 c2 : ℝ, w = c1 • e1 + c2 • e2 := hw w;
        simp_all +decide [ norm_add_sq_real, norm_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ];
        simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
        have h_norm_sq : a1^2 + a2^2 = 1 ∧ b1^2 + b2^2 = 1 := by
          have h_norm_sq : ‖a1 • e1 + a2 • e2‖^2 = a1^2 + a2^2 ∧ ‖b1 • e1 + b2 • e2‖^2 = b1^2 + b2^2 := by
            simp +decide [ norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, he1, he2, he1e2 ];
          aesop;
        grind;
      field_simp;
      rw [ ← h_inner, real_inner_comm v u ] ; ring

/-
A formula for the orthogonal projection of a point `P` onto the line passing through `A` and `B`.
-/
lemma orthogonalProjection_affineSpan_pair_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A B P : V) (h_ne : A ≠ B) :
    (orthogonalProjection (affineSpan ℝ {A, B}) P : V) =
      A + inner ℝ (P - A) (‖B - A‖⁻¹ • (B - A)) • (‖B - A‖⁻¹ • (B - A)) := by
        -- By definition of orthogonal projection, we know that the projection of $P$ onto the line spanned by $A$ and $B$ is the point $Q$ such that $Q = A + t(B - A)$ for some scalar $t$.
        have h_proj_def : ∃ t : ℝ, (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, B}) P : V) = A + t • (B - A) := by
          simp_all +decide [ affineSpan ];
          simp +decide [ spanPoints ] at *;
          have h_affine : ∀ p ∈ {p : V | (∃ v ∈ vectorSpan ℝ {A, B}, p = v + A) ∨ ∃ v ∈ vectorSpan ℝ {A, B}, p = v + B}, ∃ t : ℝ, p = A + t • (B - A) := by
            simp +decide [ vectorSpan_pair ];
            rintro p ( ⟨ v, hv, rfl ⟩ | ⟨ v, hv, rfl ⟩ ) <;> rw [ Submodule.mem_span_singleton ] at hv <;> obtain ⟨ t, rfl ⟩ := hv <;> simp +decide [ add_comm ];
            · exact ⟨ -t, by rw [ neg_smul, ← smul_neg, neg_sub ] ⟩;
            · exact ⟨ 1 - t, by simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩;
          exact h_affine _ <| Subtype.mem _;
        -- By definition of orthogonal projection, we know that the projection of $P$ onto the line spanned by $A$ and $B$ is the point $Q$ such that $Q = A + t(B - A)$ for some scalar $t$. We need to find this scalar $t$.
        obtain ⟨t, ht⟩ := h_proj_def
        have ht_value : t = ⟪P - A, ‖B - A‖⁻¹ • (B - A)⟫ * ‖B - A‖⁻¹ := by
          -- By definition of orthogonal projection, we know that the projection of $P$ onto the line spanned by $A$ and $B$ is the point $Q$ such that $Q = A + t(B - A)$ for some scalar $t$. We need to find this scalar $t$ using the inner product.
          have ht_inner : ⟪P - (A + t • (B - A)), (B - A)⟫ = 0 := by
            have h_orthogonal : ∀ (Q : V), Q ∈ affineSpan ℝ ({ A, B } : Set V) → ⟪P - (EuclideanGeometry.orthogonalProjection (affineSpan ℝ { A, B }) P : V), Q - (EuclideanGeometry.orthogonalProjection (affineSpan ℝ { A, B }) P : V)⟫ = 0 := by
              intro Q hQ;
              convert EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal ( affineSpan ℝ { A, B } ) P ( Q -ᵥ ( EuclideanGeometry.orthogonalProjection ( affineSpan ℝ { A, B } ) P : V ) ) using 1;
              simp +decide [ inner_sub_left, inner_sub_right ];
              simp +decide [ real_inner_comm, sub_eq_zero ];
              exact ⟨ fun h _ => by linarith, fun h => by linarith [ h ( AffineSubspace.vsub_mem_direction hQ ( EuclideanGeometry.orthogonalProjection_mem _ ) ) ] ⟩;
            have := h_orthogonal A ( mem_affineSpan ℝ ( Set.mem_insert _ _ ) ) ; simp_all +decide [ inner_sub_left, inner_sub_right ] ;
            simp_all +decide [ inner_add_left, inner_add_right, inner_smul_left, inner_smul_right ] ; linarith [ h_orthogonal A ( mem_affineSpan ℝ ( Set.mem_insert _ _ ) ), h_orthogonal B ( mem_affineSpan ℝ ( Set.mem_insert_of_mem _ ( Set.mem_singleton _ ) ) ) ] ;
          by_cases h : ‖B - A‖ = 0 <;> simp_all +decide [ inner_sub_left, inner_smul_right ];
          · exact False.elim ( h_ne ( sub_eq_zero.mp h ▸ rfl ) );
          · simp_all +decide [ inner_add_left, inner_smul_left ];
            simp_all +decide [ inner_self_eq_norm_sq_to_K, sub_eq_iff_eq_add ];
            simp +decide [ sq, mul_assoc, mul_comm, ne_of_gt ( norm_pos_iff.mpr ( sub_ne_zero.mpr h ) ) ];
        simp_all +decide [ MulAction.mul_smul ]

end AristotleLemmas

lemma dist_projections_eq_dist_mul_sin {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
    let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
    dist Pb Pc = dist P A * Real.sin (∠ B A C) := by
  -- By definition of $Pb$ and $Pc$, we have $Pb = A + (P - A) · (‖C - A‖⁻¹ • (C - A)) · (‖C - A‖⁻¹ • (C - A))$ and $Pc = A + (P - A) · (‖B - A‖⁻¹ • (B - A)) · (‖B - A‖⁻¹ • (B - A))$.
  set u := ‖C - A‖⁻¹ • (C - A)
  set v := ‖B - A‖⁻¹ • (B - A)
  have hPb : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P : V) = A + inner ℝ (P - A) u • u := by
    convert orthogonalProjection_affineSpan_pair_eq A C P _ using 1;
    exact fun h => h_triangle <| by rw [ h ] ; simp +decide [ collinear_pair ] ;
  have hPc : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P : V) = A + inner ℝ (P - A) v • v := by
    convert orthogonalProjection_affineSpan_pair_eq A B P _ using 1;
    rintro rfl; simp_all +decide [ collinear_pair ];
  -- The squared norm of the difference of projections is $\|P - A\|^2 (1 - \langle u, v \rangle^2)$.
  have h_diff_sq : ‖(inner ℝ (P - A) v • v - inner ℝ (P - A) u • u)‖^2 = ‖P - A‖^2 * (1 - (inner ℝ u v)^2) := by
    convert norm_inner_smul_sub_inner_smul_sq_of_dim_two u v ( P - A ) _ _ using 1;
    · rw [ norm_smul, norm_inv, Real.norm_of_nonneg ( norm_nonneg _ ), inv_mul_cancel₀ ( norm_ne_zero_iff.mpr <| sub_ne_zero.mpr <| by rintro rfl; simp_all +decide [ collinear_pair ] ) ];
    · rw [ norm_smul, norm_inv, Real.norm_of_nonneg ( norm_nonneg _ ), inv_mul_cancel₀ ( norm_ne_zero_iff.mpr <| sub_ne_zero.mpr <| by rintro rfl; simp_all +decide [ collinear_pair ] ) ];
  -- Since $\sin^2(\theta) = 1 - \cos^2(\theta)$, we can rewrite the right-hand side of the equation.
  have h_sin_sq : 1 - (inner ℝ u v)^2 = (Real.sin (∠ B A C))^2 := by
    rw [ EuclideanGeometry.angle, Real.sin_sq, Real.cos_sq' ];
    rw [ Real.sin_sq, InnerProductGeometry.cos_angle ];
    simp +zetaDelta at *;
    simp +decide [ div_eq_inv_mul, mul_comm, mul_left_comm, inner_smul_left, inner_smul_right ];
    rw [ real_inner_comm ];
  simp_all +decide [ dist_eq_norm ];
  rw [ ← Real.sqrt_sq ( norm_nonneg _ ), ← Real.sqrt_sq ( mul_nonneg ( norm_nonneg _ ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( EuclideanGeometry.angle_nonneg _ _ _ ) ( EuclideanGeometry.angle_le_pi _ _ _ ) ) ) ];
  rw [ norm_sub_rev, h_diff_sq, mul_pow ]

/- Projection inequality: dist(Pb, Pc) ≥ d₂ * sin C + d₃ * sin B. -/
noncomputable section AristotleLemmas

/-
Trigonometric inequality for the projection lemma.
-/
lemma trig_ineq_of_sum_pi (A B C α₁ α₂ : ℝ) (h_sum : A + B + C = Real.pi) (h_split : α₁ + α₂ = A) (hA : 0 ≤ Real.sin A) :
    Real.sin α₂ * Real.sin C + Real.sin α₁ * Real.sin B ≤ Real.sin A := by
      -- Substitute C = π - (A + B) and A = α₁ + α₂ into the inequality.
      have h_subst : Real.sin α₂ * Real.sin (Real.pi - (α₁ + α₂ + B)) + Real.sin α₁ * Real.sin B ≤ Real.sin (α₁ + α₂) := by
        norm_num [ Real.sin_add, Real.cos_add ];
        -- Factor out common terms and simplify the expression.
        suffices h_simp : (Real.sin α₁ * Real.cos α₂ + Real.cos α₁ * Real.sin α₂) * (Real.sin α₂ * Real.cos B + Real.cos α₂ * Real.sin B) ≤ Real.sin α₁ * Real.cos α₂ + Real.cos α₁ * Real.sin α₂ by
          convert h_simp using 1 ; ring_nf;
          rw [ Real.cos_sq' ] ; ring;
        refine' mul_le_of_le_one_right _ _;
        · rw [ ← Real.sin_add ] ; aesop;
        · nlinarith only [ sq_nonneg ( Real.sin α₂ - Real.cos B ), sq_nonneg ( Real.cos α₂ - Real.sin B ), Real.sin_sq_add_cos_sq α₂, Real.sin_sq_add_cos_sq B ];
      convert h_subst using 2 <;> subst_vars <;> ring_nf;
      exact congrArg _ ( congrArg Real.sin ( by linarith ) )

/-
Distance from a point to a line is the distance to the reference point times the sine of the angle.
-/
lemma dist_projection_eq_dist_mul_sin {A B P : V} (h : A ≠ B) :
    dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P) = dist P A * Real.sin (∠ P A B) := by
      -- By definition of orthogonal projection, we know that the orthogonal projection of $P$ onto the line $AB$ is the point where the perpendicular from $P$ meets the line $AB$.
      let Q := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, B})) P
      have hQ : (dist P Q) = (dist P A) * Real.sin (∠ P A (Q : V)) := by
        rw [ EuclideanGeometry.angle, dist_eq_norm, dist_eq_norm ];
        -- By definition of orthogonal projection, we know that $P - Q$ is orthogonal to $Q - A$.
        have h_orthogonal : inner ℝ (P - Q) (Q - A) = 0 := by
          have hQ_ortho : ∀ (v : V), v ∈ (affineSpan ℝ {A, B}).direction → ⟪P - (Q : V), v⟫ = 0 := by
            intro v hv;
            simp +decide [ inner_sub_left ];
            rw [ real_inner_comm v, real_inner_comm v ] ; ring_nf!;
            have := EuclideanGeometry.orthogonalProjection_mem_orthogonal ( affineSpan ℝ { A, B } ) P v hv; simp_all +decide [ inner_sub_right ] ;
            linarith;
          convert hQ_ortho ( Q - A ) _ using 1;
          exact AffineSubspace.vsub_mem_direction ( show ( Q : V ) ∈ affineSpan ℝ { A, B } from Q.2 ) ( show A ∈ affineSpan ℝ { A, B } from mem_affineSpan ℝ ( Set.mem_insert _ _ ) );
        rw [ InnerProductGeometry.angle, Real.sin_arccos ];
        field_simp;
        by_cases h : P -ᵥ A = 0 <;> by_cases h' : ( Q : V ) -ᵥ A = 0 <;> simp_all +decide [ sub_eq_iff_eq_add, inner_sub_left, inner_sub_right ];
        · have := EuclideanGeometry.orthogonalProjection_eq_self_iff.mpr ( show A ∈ affineSpan ℝ { A, B } from mem_affineSpan ℝ ( Set.mem_insert _ _ ) ) ; aesop;
        · rw [ one_sub_div ];
          · rw [ ← Real.sqrt_sq ( norm_nonneg _ ), mul_comm ];
            rw [ show ‖P - ( Q : V )‖ ^ 2 = ‖P - A‖ ^ 2 - 2 * ⟪P - A, ( Q : V ) - A⟫ + ‖( Q : V ) - A‖ ^ 2 by
                  rw [ @norm_sub_sq ℝ, @norm_sub_sq ℝ, @norm_sub_sq ℝ ];
                  simp +decide [ inner_sub_left, inner_sub_right, h_orthogonal ] ; ring_nf;
                  simp +decide [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring ];
            rw [ show ‖P - A‖ ^ 2 - 2 * ⟪P - A, ( Q : V ) - A⟫ + ‖( Q : V ) - A‖ ^ 2 = ( ‖P - A‖ ^ 2 * ‖( Q : V ) - A‖ ^ 2 - ( ⟪P, A⟫ - ⟪( Q : V ), A⟫ + ⟪( Q : V ), ( Q : V )⟫ - ⟪A, ( Q : V )⟫ - ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) / ( ‖( Q : V ) - A‖ ^ 2 ) from ?_ ];
            · rw [ show ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 - ( ⟪P, A⟫ - ⟪ ( Q : V ), A⟫ + ⟪ ( Q : V ), ( Q : V )⟫ - ⟪A, ( Q : V )⟫ - ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) / ‖ ( Q : V ) - A‖ ^ 2 = ( ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 - ( ⟪P, A⟫ - ⟪ ( Q : V ), A⟫ + ⟪ ( Q : V ), ( Q : V )⟫ - ⟪A, ( Q : V )⟫ - ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) / ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 ) ) * ‖P - A‖ ^ 2 by rw [ div_mul_eq_mul_div, div_eq_div_iff ] <;> ring_nf <;> simp +decide [ sub_eq_iff_eq_add, h, h' ] ] ; rw [ Real.sqrt_mul' _ ( by positivity ), Real.sqrt_sq ( by positivity ) ] ;
            · rw [ eq_div_iff ( pow_ne_zero _ <| norm_ne_zero_iff.mpr <| sub_ne_zero.mpr h' ) ] ; simp +decide [ *, inner_sub_left, inner_sub_right, norm_sub_sq_real ] ; ring_nf;
              norm_num [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring;
          · exact mul_ne_zero ( pow_ne_zero 2 ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr h ) ) ) ( pow_ne_zero 2 ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr h' ) ) );
      -- Since $Q$ lies on the line $AB$, we have $\angle PAQ = \angle PAB$ or $\angle PAQ = \pi - \angle PAB$.
      have h_angle : ∠ P A (Q : V) = ∠ P A B ∨ ∠ P A (Q : V) = Real.pi - ∠ P A B := by
        -- Since $Q$ lies on the line $AB$, we can express $Q$ as $Q = A + t(B - A)$ for some scalar $t$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, Q = A + t • (B - A) := by
          have hQ_affine : Q.val ∈ affineSpan ℝ {A, B} := by
            exact Q.2;
          rcases hQ_affine with ⟨ t, ht ⟩;
          rcases ht with ⟨ rfl | rfl, v, hv, hv' ⟩ <;> simp_all +decide [ vectorSpan_pair ];
          · rw [ Submodule.mem_span_singleton ] at hv;
            rcases hv with ⟨ a, rfl ⟩ ; exact ⟨ -a, by simp +decide [ add_comm, smul_neg, neg_smul, sub_eq_add_neg ] ⟩ ;
          · rw [ Submodule.mem_span_singleton ] at hv;
            rcases hv with ⟨ a, rfl ⟩ ; exact ⟨ 1 - a, by simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩ ;
        by_cases h : t = 0 <;> simp_all +decide [ EuclideanGeometry.angle ];
        · have h_orthogonal : inner ℝ (P - A) (B - A) = 0 := by
            have := EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal ( affineSpan ℝ { A, B } ) P;
            simp_all +decide [ Submodule.mem_orthogonal', direction_affineSpan ];
            specialize this ( B - A ) ( by exact Submodule.subset_span ( by simp +decide [ Set.mem_vsub ] ) ) ; simp_all +decide [ inner_sub_left, inner_sub_right ] ;
            simp +zetaDelta at *;
            simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
            linarith;
          by_cases hP : P = A <;> by_cases hB : B = A <;> simp_all +decide [ InnerProductGeometry.angle ];
        · cases lt_or_gt_of_ne h <;> simp +decide [ *, InnerProductGeometry.angle_smul_right_of_pos, InnerProductGeometry.angle_smul_right_of_neg ];
          rw [ show A - B = - ( B - A ) by abel1, InnerProductGeometry.angle_neg_right ] ; aesop;
      aesop

/-
The angle between u and v is the sum of the angle between u and u+v and the angle between u+v and v.
-/
lemma angle_add_eq_angle_of_add {u v : V} (h_indep : ¬ Collinear ℝ ({0, u, v} : Set V)) :
    InnerProductGeometry.angle u (u + v) + InnerProductGeometry.angle (u + v) v = InnerProductGeometry.angle u v := by
      -- By the properties of the angle function, we know that $\angle u w + \angle w v = \angle u v$.
      have h_angle_add : Real.arccos (inner ℝ u (u + v) / (‖u‖ * ‖u + v‖)) + Real.arccos (inner ℝ (u + v) v / (‖u + v‖ * ‖v‖)) = Real.arccos (inner ℝ u v / (‖u‖ * ‖v‖)) := by
        by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> by_cases hw : u + v = 0 <;> simp_all +decide [ inner_add_right, inner_add_left, mul_comm ];
        · exact False.elim ( h_indep <| collinear_singleton _ _ );
        · simp +decide [ ← sq, inner_self_eq_norm_sq_to_K ];
          rw [ div_self ( pow_ne_zero _ ( norm_ne_zero_iff.mpr hv ) ) ];
        · simp +decide [ inner_self_eq_norm_sq_to_K ];
          rw [ sq, div_self ( ne_of_gt ( mul_pos ( norm_pos_iff.mpr hu ) ( norm_pos_iff.mpr hu ) ) ) ];
        · simp_all +decide [ add_eq_zero_iff_eq_neg ];
          simp_all +decide [ inner_self_eq_norm_sq_to_K ];
          simp +decide [ ← sq, hv ];
        · -- By the properties of the angle function, we know that $\cos(\angle u w + \angle w v) = \cos(\angle u v)$.
          have h_cos_add : Real.cos (Real.arccos ((⟪u, u⟫ + ⟪u, v⟫) / (‖u‖ * ‖u + v‖)) + Real.arccos ((⟪u, v⟫ + ⟪v, v⟫) / (‖v‖ * ‖u + v‖))) = Real.cos (Real.arccos (⟪u, v⟫ / (‖u‖ * ‖v‖))) := by
            rw [ Real.cos_add, Real.cos_arccos, Real.sin_arccos, Real.cos_arccos, Real.sin_arccos ];
            · rw [ Real.cos_arccos ];
              · field_simp;
                rw [ Real.sqrt_div ( _ ), Real.sqrt_div ( _ ) ];
                · field_simp;
                  rw [ show ‖u‖ ^ 2 * ‖u + v‖ ^ 2 - ( ⟪u, u⟫ + ⟪u, v⟫ ) ^ 2 = ( ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 ) by
                        norm_num [ @norm_add_sq ℝ, inner_add_right, inner_add_left ] ; ring_nf;
                        rw [ real_inner_self_eq_norm_sq ] ; ring, show ‖u + v‖ ^ 2 * ‖v‖ ^ 2 - ( ⟪u, v⟫ + ⟪v, v⟫ ) ^ 2 = ( ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 ) by
                                                                                                                            rw [ @norm_add_sq ℝ ] ; ring_nf;
                                                                                                                            norm_num [ real_inner_self_eq_norm_sq ] ; ring_nf ];
                  rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_mul ( by positivity ) ];
                  rw [ Real.sqrt_sq ( norm_nonneg _ ), Real.sqrt_sq ( norm_nonneg _ ), Real.sqrt_sq ( norm_nonneg _ ) ] ; ring_nf;
                  rw [ Real.sq_sqrt ];
                  · rw [ show ‖u + v‖ ^ 4 = ( ‖u + v‖ ^ 2 ) ^ 2 by ring, norm_add_sq_real ] ; ring_nf;
                    rw [ show ‖u‖ ^ 5 = ‖u‖ ^ 3 * ‖u‖ ^ 2 by ring, show ‖v‖ ^ 5 = ‖v‖ ^ 3 * ‖v‖ ^ 2 by ring, show ‖u‖ ^ 3 = ‖u‖ * ‖u‖ ^ 2 by ring, show ‖v‖ ^ 3 = ‖v‖ * ‖v‖ ^ 2 by ring ] ; rw [ real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq ] ; ring;
                  · nlinarith [ abs_le.mp ( abs_real_inner_le_norm u v ) ];
                · have := abs_le.mp ( abs_real_inner_le_norm ( u + v ) v );
                  simp_all +decide [ inner_add_left ];
                  nlinarith [ norm_nonneg ( u + v ), norm_nonneg v ];
                · norm_num [ real_inner_self_eq_norm_sq ];
                  rw [ @norm_add_sq ℝ ];
                  nlinarith! [ sq_nonneg ( ‖u‖ ^ 2 - ‖v‖ ^ 2 ), abs_le.mp ( abs_real_inner_le_norm u v ) ];
              · exact ( abs_le.mp ( abs_real_inner_div_norm_mul_norm_le_one u v ) ) |>.1;
              · exact div_le_one_of_le₀ ( by linarith [ abs_le.mp ( abs_real_inner_le_norm u v ) ] ) ( mul_nonneg ( norm_nonneg u ) ( norm_nonneg v ) );
            · rw [ le_div_iff₀ ( mul_pos ( norm_pos_iff.mpr hv ) ( norm_pos_iff.mpr hw ) ) ];
              have := norm_add_le ( u + v ) ( -v ) ; simp_all +decide [ norm_neg ];
              nlinarith [ norm_nonneg u, norm_nonneg v, norm_nonneg ( u + v ), norm_add_sq_real u v, norm_add_sq_real v ( u + v ), norm_add_sq_real u ( u + v ), real_inner_self_eq_norm_sq u, real_inner_self_eq_norm_sq v, real_inner_self_eq_norm_sq ( u + v ) ];
            · refine' div_le_one_of_le₀ _ _ <;> norm_num [ real_inner_self_eq_norm_sq ];
              · have := norm_add_sq_real u v ; simp_all +decide ; nlinarith [ norm_nonneg u, norm_nonneg v, norm_nonneg ( u + v ), abs_le.mp ( abs_real_inner_le_norm u v ), abs_le.mp ( abs_real_inner_le_norm v ( u + v ) ) ] ;
              · positivity;
            · rw [ le_div_iff₀ ( mul_pos ( norm_pos_iff.mpr hu ) ( norm_pos_iff.mpr hw ) ) ];
              simp +decide [ ← inner_add_right ];
              exact neg_le_of_abs_le ( by simpa [ abs_mul ] using abs_real_inner_le_norm u ( u + v ) );
            · field_simp;
              convert abs_le.mp ( abs_real_inner_le_norm u ( u + v ) ) |> And.right using 1 ; simp +decide [ inner_add_right ];
          rw [ Real.injOn_cos ⟨ ?_, ?_ ⟩ ⟨ ?_, ?_ ⟩ h_cos_add ];
          · exact add_nonneg ( Real.arccos_nonneg _ ) ( Real.arccos_nonneg _ );
          · rw [ Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin ];
            -- By simplifying, we can see that this inequality holds because the arcsin function is increasing.
            have h_arcsin_inc : (⟪u, u⟫ + ⟪u, v⟫) / (‖u‖ * ‖u + v‖) ≥ -((⟪u, v⟫ + ⟪v, v⟫) / (‖v‖ * ‖u + v‖)) := by
              field_simp;
              norm_num [ real_inner_self_eq_norm_sq ] at *;
              nlinarith [ norm_nonneg u, norm_nonneg v, mul_nonneg ( norm_nonneg u ) ( norm_nonneg v ), abs_le.mp ( abs_real_inner_le_norm u v ) ];
            have h_arcsin_inc : Real.arcsin ((⟪u, u⟫ + ⟪u, v⟫) / (‖u‖ * ‖u + v‖)) ≥ Real.arcsin (-((⟪u, v⟫ + ⟪v, v⟫) / (‖v‖ * ‖u + v‖))) := by
              exact Real.monotone_arcsin h_arcsin_inc;
            rw [ Real.arcsin_neg ] at h_arcsin_inc ; linarith;
          · exact Real.arccos_nonneg _;
          · exact Real.arccos_le_pi _;
      rwa [ InnerProductGeometry.angle, InnerProductGeometry.angle, InnerProductGeometry.angle ]

/-
If 0, u, v are not collinear and k is non-zero, then 0, u, k*v are not collinear.
-/
lemma not_collinear_smul_right {u v : V} (h : ¬ Collinear ℝ ({0, u, v} : Set V)) (k : ℝ) (hk : k ≠ 0) : ¬ Collinear ℝ ({0, u, k • v} : Set V) := by
  simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
  intro a b x hx y hy z hz
  have h_collinear : Collinear ℝ ({0, u, v} : Set V) := by
    rw [ collinear_iff_exists_forall_eq_smul_vadd ];
    use 0, b;
    simp_all +decide [ ← eq_sub_iff_add_eq' ];
    refine' ⟨ ⟨ 0, _ ⟩, ⟨ -x + y, _ ⟩, ⟨ k⁻¹ * z - k⁻¹ * x, _ ⟩ ⟩ <;> simp +decide [ ← hx ];
    · rw [ eq_comm ] at hx ; simp_all +decide [ add_smul ];
      exact eq_neg_of_add_eq_zero_right hx;
    · simp +decide [ ← mul_sub ];
      rw [ show a = -x • b by rw [ eq_comm, add_eq_zero_iff_eq_neg ] at hx; simp_all +decide ] at hz;
      rw [ show v = k⁻¹ • ( k • v ) by rw [ inv_smul_smul₀ hk ] ] ; rw [ hz ] ; simp +decide [ smul_smul ];
      simp +decide [ mul_sub, sub_smul ];
      grind;
  rw [ collinear_iff_exists_forall_eq_smul_vadd ] at h_collinear;
  obtain ⟨ p₀, v₁, hp₀ ⟩ := h_collinear; specialize h p₀ v₁; simp_all +decide [ add_comm ] ;
  exact h _ hp₀.1.choose_spec _ hp₀.2.1.choose_spec _ hp₀.2.2.choose_spec

/-
If w is a positive linear combination of linearly independent vectors u and v, then the angle between u and v is the sum of the angle between u and w and the angle between w and v.
-/
lemma angle_add_of_positive_linear_combination {u v : V} (h_indep : ¬ Collinear ℝ ({0, u, v} : Set V)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    InnerProductGeometry.angle u (a • u + b • v) + InnerProductGeometry.angle (a • u + b • v) v = InnerProductGeometry.angle u v := by
      -- Let $w = (b/a)v$. Then $u + w = u + (b/a)v$.
      set w : V := (b / a) • v;
      -- By the properties of the angle function, we have $\angle(u, a \bullet u + b \bullet v) = \angle(u, u + w)$ and $\angle(a \bullet u + b \bullet v, v) = \angle(u + w, v)$.
      have h_angle_eq : InnerProductGeometry.angle u (a • u + b • v) = InnerProductGeometry.angle u (u + w) ∧ InnerProductGeometry.angle (a • u + b • v) v = InnerProductGeometry.angle (u + w) v := by
        have h_angle_eq : a • u + b • v = a • (u + w) := by
          simp +zetaDelta at *;
          simp +decide [ ← smul_assoc, mul_div_cancel₀ _ ha.ne' ];
        simp +decide [ h_angle_eq ];
        simp +decide [ ← smul_add, InnerProductGeometry.angle_smul_left_of_pos, InnerProductGeometry.angle_smul_right_of_pos, ha ];
      -- By the properties of the angle function, we have $\angle(u, u + w) + \angle(u + w, w) = \angle(u, w)$.
      have h_angle_sum : InnerProductGeometry.angle u (u + w) + InnerProductGeometry.angle (u + w) w = InnerProductGeometry.angle u w := by
        apply angle_add_eq_angle_of_add;
        convert not_collinear_smul_right h_indep ( b / a ) ( div_ne_zero hb.ne' ha.ne' ) using 1;
      aesop

/-
If P is in the interior of triangle ABC, then P - A is a positive linear combination of B - A and C - A.
-/
lemma exists_pos_linear_combination_of_mem_interior_triangle {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V)) (h_interior : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ P - A = a • (B - A) + b • (C - A) := by
      -- By `AffineBasis.interior_convexHull`, since $P$ is in the interior of the convex hull, its barycentric coordinates with respect to $b$ are strictly positive.
      obtain ⟨coords, hcoords⟩ : ∃ coords : Fin 3 → ℝ, (∀ i, 0 < coords i) ∧ (∑ i, coords i = 1) ∧ P = ∑ i, coords i • ![A, B, C] i := by
        -- By `AffineBasis.interior_convexHull`, since $P$ is in the interior of the convex hull of $\{A, B, C\}$, there exist coordinates $coords : Fin 3 → ℝ$ such that $P = \sum_{i=0}^2 coords i • ![A, B, C] i$ and $0 < coords i$ for all $i$.
        have h_coords : P ∈ interior (convexHull ℝ {A, B, C}) → ∃ coords : Fin 3 → ℝ, (∀ i, 0 < coords i) ∧ (∑ i, coords i = 1) ∧ P = ∑ i, coords i • ![A, B, C] i := by
          intro hP_interior
          obtain ⟨b, hb⟩ : ∃ b : AffineBasis (Fin 3) ℝ V, b 0 = A ∧ b 1 = B ∧ b 2 = C := by
            have h_affine_basis : AffineIndependent ℝ ![A, B, C] := by
              exact affineIndependent_iff_not_collinear_set.mpr h_triangle
            refine' ⟨ _, _, _, _ ⟩;
            refine' { .. };
            use ![A, B, C];
            grind;
            any_goals rfl;
            refine' eq_top_iff.mpr _;
            intro x hx;
            have h_span : Submodule.span ℝ (Set.range ![A - C, B - C]) = ⊤ := by
              refine' Submodule.eq_top_of_finrank_eq _;
              rw [ finrank_span_eq_card ] <;> norm_num [ hV.1 ];
              rw [ linearIndependent_fin2 ];
              simp_all +decide [ sub_eq_iff_eq_add, affineIndependent_iff_not_collinear ];
              refine' ⟨ _, _ ⟩;
              · rintro rfl; simp_all +decide [ collinear_pair ];
              · contrapose! h_triangle;
                rw [ collinear_iff_exists_forall_eq_smul_vadd ];
                obtain ⟨ a, ha ⟩ := h_triangle;
                exact ⟨ C, B - C, fun p hp => by rcases hp with ( rfl | rfl | rfl ) <;> [ exact ⟨ a, by simpa [ sub_eq_iff_eq_add ] using ha.symm ⟩ ; exact ⟨ 1, by simp +decide ⟩ ; exact ⟨ 0, by simp +decide ⟩ ] ⟩;
            rw [ Submodule.eq_top_iff' ] at h_span;
            specialize h_span ( x - C );
            rw [ Submodule.mem_span_range_iff_exists_fun ] at h_span;
            obtain ⟨ c, hc ⟩ := h_span;
            simp_all +decide [ spanPoints ];
            refine' Or.inl ⟨ c 0 • ( A - C ) + c 1 • ( B - C ), _, _ ⟩ <;> simp_all +decide [ vectorSpan ];
            rw [ ← hc ];
            refine' Submodule.add_mem _ _ _;
            · exact Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ A, by simp +decide, C, by simp +decide, rfl ⟩ );
            · refine' Submodule.smul_mem _ _ _;
              exact Submodule.subset_span ⟨ B, by simp +decide, C, by simp +decide, rfl ⟩;
          -- By `AffineBasis.interior_convexHull`, since $P$ is in the interior of the convex hull of $\{A, B, C\}$, its barycentric coordinates with respect to $b$ are strictly positive.
          have h_coords_pos : ∀ (x : V), x ∈ interior (convexHull ℝ (Set.range b)) → ∃ coords : Fin 3 → ℝ, (∀ i, 0 < coords i) ∧ (∑ i, coords i = 1) ∧ x = ∑ i, coords i • b i := by
            intro x hx_interior
            obtain ⟨coords, hcoords⟩ : ∃ coords : Fin 3 → ℝ, (∀ i, 0 < coords i) ∧ (∑ i, coords i = 1) ∧ x = ∑ i, coords i • b i := by
              have h_coords_pos : ∀ (x : V), x ∈ interior (convexHull ℝ (Set.range b)) → ∀ i, 0 < b.coord i x := by
                rw [AffineBasis.interior_convexHull] at *; aesop;
              refine' ⟨ _, h_coords_pos x hx_interior, _, _ ⟩;
              · exact b.sum_coord_apply_eq_one x;
              · exact Eq.symm (AffineBasis.linear_combination_coord_eq_self b x);
            use coords;
          convert h_coords_pos P _;
          · exact funext fun i => by fin_cases i <;> tauto;
          · convert hP_interior using 1;
            rw [ show ( Set.range b : Set V ) = { A, B, C } by ext x; exact ⟨ fun hx => by rcases hx with ⟨ i, rfl ⟩ ; fin_cases i <;> simp +decide [ hb ], fun hx => by rcases hx with ( rfl | rfl | rfl ) <;> [ exact ⟨ 0, hb.1 ⟩ ; exact ⟨ 1, hb.2.1 ⟩ ; exact ⟨ 2, hb.2.2 ⟩ ] ⟩ ];
        exact h_coords h_interior;
      simp_all +decide [ Fin.sum_univ_three ];
      exact ⟨ coords 1, hcoords.1 1, coords 2, hcoords.1 2, by rw [ show coords 0 = 1 - coords 1 - coords 2 by linarith ] ; simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩

/-
If P is in the interior of triangle ABC, then angle BAP + angle PAC = angle BAC.
-/
lemma angle_split_of_interior {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V)) (h_interior : P ∈ interior (convexHull ℝ {A, B, C})) : ∠ B A P + ∠ P A C = ∠ B A C := by
  -- Use `exists_pos_linear_combination_of_mem_interior_triangle` to get $a, b > 0$ such that $P - A = a(B - A) + b(C - A)$.
  obtain ⟨a, b, ha, hb, h_comb⟩ : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ P - A = a • (B - A) + b • (C - A) := exists_pos_linear_combination_of_mem_interior_triangle h_triangle h_interior;
  -- Let $u = B - A$ and $v = C - A$. Since $A, B, C$ are not collinear, $u$ and $v$ are linearly independent, so $0, u, v$ are not collinear.
  set u : V := B - A
  set v : V := C - A
  have h_indep : ¬ Collinear ℝ ({0, u, v} : Set V) := by
    simp_all +decide [ collinear_iff_exists_forall_eq_smul_vadd ];
    contrapose! h_triangle;
    obtain ⟨ x, y, z, hz, w, hw, u, hu ⟩ := h_triangle; use x + A, y, z; simp_all +decide [ sub_eq_iff_eq_add ] ;
    grind;
  -- Apply `angle_add_of_positive_linear_combination` to $u, v, a, b$.
  have h_angle_add : InnerProductGeometry.angle u (P - A) + InnerProductGeometry.angle (P - A) v = InnerProductGeometry.angle u v := by
    convert angle_add_of_positive_linear_combination h_indep a b ha hb using 1 ; aesop ( simp_config := { singlePass := true } ) ;
  convert h_angle_add using 1

end AristotleLemmas

lemma dist_projections_ge_projection_on_side {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
    let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
    dist Pb Pc ≥ dist P Pb * Real.sin (∠ A C B) + dist P Pc * Real.sin (∠ A B C) := by
  -- By `dist_projections_eq_dist_mul_sin`, we have `dist Pb Pc = dist P A * sin A`.
  set Pb : V := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, C}) P : V)
  set Pc : V := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, B}) P : V)
  have h_dist_Pb_Pc : dist Pb Pc = dist P A * Real.sin (∠ B A C) := by
    exact dist_projections_eq_dist_mul_sin h_triangle;
  -- By `dist_projection_eq_dist_mul_sin`, we have `dist P Pb = dist P A * sin(∠ PAC)` and `dist P Pc = dist P A * sin(∠ PAB)`.
  have h_dist_P_Pb : dist P Pb = dist P A * Real.sin (∠ P A C) := by
    convert dist_projection_eq_dist_mul_sin _ using 2;
    · infer_instance;
    · exact hV;
    · rintro rfl; simp_all +decide [ collinear_pair ] ;
  have h_dist_P_Pc : dist P Pc = dist P A * Real.sin (∠ P A B) := by
    convert dist_projection_eq_dist_mul_sin _ using 1;
    · infer_instance;
    · exact hV;
    · rintro rfl; simp_all +decide [ collinear_pair ];
  -- By `angle_split_of_interior`, we have `∠ PAB + ∠ PAC = ∠ BAC`.
  have h_angle_split : ∠ P A B + ∠ P A C = ∠ B A C := by
    convert angle_split_of_interior h_triangle h_interior using 1;
    rw [ EuclideanGeometry.angle_comm B A P ];
  -- By `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`, we have `∠ BAC + ∠ ABC + ∠ ACB = pi`.
  have h_angle_sum : ∠ B A C + ∠ A B C + ∠ A C B = Real.pi := by
    have h_angle_sum : ∀ (p₁ p₂ p₃ : V), p₂ ≠ p₁ → angle p₁ p₂ p₃ + angle p₂ p₃ p₁ + angle p₃ p₁ p₂ = Real.pi := by
      exact fun p₁ p₂ p₃ a => angle_add_angle_add_angle_eq_pi p₃ a;
    convert h_angle_sum A B C ( by rintro rfl; simp_all +decide [ collinear_pair ] ) using 1;
    simp +decide only [angle_comm] ; ring;
  -- By `trig_ineq_of_sum_pi`, we have `sin(∠ PAC) * sin(∠ ACB) + sin(∠ PAB) * sin(∠ ABC) ≤ sin(∠ BAC)`.
  have h_trig_ineq : Real.sin (∠ P A C) * Real.sin (∠ A C B) + Real.sin (∠ P A B) * Real.sin (∠ A B C) ≤ Real.sin (∠ B A C) := by
    convert trig_ineq_of_sum_pi ( ∠ B A C ) ( ∠ A B C ) ( ∠ A C B ) ( ∠ P A B ) ( ∠ P A C ) _ _ _ using 1 <;> linarith [ Real.sin_nonneg_of_nonneg_of_le_pi ( show 0 ≤ ∠ B A C by exact EuclideanGeometry.angle_nonneg _ _ _ ) ( show ∠ B A C ≤ Real.pi by exact EuclideanGeometry.angle_le_pi _ _ _ ) ];
  field_simp;
  rw [ h_dist_Pb_Pc, h_dist_P_Pb, h_dist_P_Pc ] ; nlinarith [ @dist_nonneg _ _ P A ] ;

/-- The core lemma for Erdős-Mordell: R₁ ≥ d₂ * (c/a) + d₃ * (b/a) -/
lemma erdos_898_lemma {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    dist P A ≥ dist_to_line P A C * (dist A B / dist B C) + dist_to_line P A B * (dist A C / dist B C) := by
  let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
  let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
  have h_ne_BC : B ≠ C := by intro h; subst h; apply h_triangle; rw [show ({A, B, B} : Set V) = {A, B} by ext x; simp]; apply collinear_pair
  have h_ne_AC : A ≠ C := by intro h; subst h; apply h_triangle; rw [show ({A, B, A} : Set V) = {A, B} by ext x; simp; tauto]; apply collinear_pair
  have h_ne_AB : A ≠ B := by intro h; subst h; apply h_triangle; rw [show ({A, A, C} : Set V) = {A, C} by ext x; simp]; apply collinear_pair

  have h_pedal : dist Pb Pc = dist P A * Real.sin (∠ B A C) := dist_projections_eq_dist_mul_sin h_triangle
  have h_proj : dist Pb Pc ≥ dist P Pb * Real.sin (∠ A C B) + dist P Pc * Real.sin (∠ A B C) := dist_projections_ge_projection_on_side h_triangle h_interior
  rw [h_pedal] at h_proj

  have h_sin_pos : 0 < Real.sin (∠ B A C) := sin_pos_of_not_collinear (by rwa [show ({B, A, C} : Set V) = {A, B, C} by ext x; simp; tauto])

  have h_sin_rule_C : Real.sin (∠ A C B) = Real.sin (∠ B A C) * dist A B / dist B C := by
    have h := sin_angle_div_dist_eq_sin_angle_div_dist (p₁ := A) (p₂ := C) (p₃ := B) h_ne_BC.symm h_ne_AB.symm
    replace h := (div_eq_iff (dist_pos.mpr h_ne_AB.symm).ne').mp h
    rw [h, angle_comm B A C, dist_comm B A, dist_comm C B]
    field_simp [dist_pos.mpr h_ne_BC]

  have h_sin_rule_B : Real.sin (∠ A B C) = Real.sin (∠ B A C) * dist A C / dist B C := by
    have h := sin_angle_div_dist_eq_sin_angle_div_dist (p₁ := A) (p₂ := B) (p₃ := C) h_ne_BC h_ne_AC.symm
    replace h := (div_eq_iff (dist_pos.mpr h_ne_AC.symm).ne').mp h
    rw [h, angle_comm C A B, angle_comm B A C, dist_comm C A, dist_comm B C]
    field_simp [dist_pos.mpr h_ne_BC]

  rw [h_sin_rule_C, h_sin_rule_B] at h_proj
  have d₂_eq : dist P Pb = dist_to_line P A C := rfl
  have d₃_eq : dist P Pc = dist_to_line P A B := rfl
  rw [d₂_eq, d₃_eq] at h_proj
  field_simp [dist_pos.mpr h_ne_BC, h_sin_pos.ne'] at h_proj ⊢
  nlinarith

/-- A simple AM-GM consequence: x/y + y/x ≥ 2 for positive x, y. -/
lemma add_div_self_ge_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x / y + y / x ≥ 2 := by
  have h_sq : 0 ≤ (x - y)^2 := pow_two_nonneg (x - y)
  have h_exp : (x - y)^2 = x^2 - 2 * x * y + y^2 := by ring
  rw [h_exp] at h_sq
  have h_add : 2 * x * y ≤ x^2 + y^2 := by linarith
  field_simp [hx.ne', hy.ne']
  linarith

/-- Erdős-Mordell Inequality summation. -/
lemma erdos_898_summation (R₁ R₂ R₃ d₁ d₂ d₃ a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd1 : 0 ≤ d₁) (hd2 : 0 ≤ d₂) (hd3 : 0 ≤ d₃)
    (h₁ : R₁ ≥ d₂ * (c/a) + d₃ * (b/a))
    (h₂ : R₂ ≥ d₃ * (a/b) + d₁ * (c/b))
    (h₃ : R₃ ≥ d₁ * (b/c) + d₂ * (a/c)) :
    R₁ + R₂ + R₃ ≥ 2 * (d₁ + d₂ + d₃) := by
  let S := R₁ + R₂ + R₃
  have h_sum : S ≥ d₁ * (b/c + c/b) + d₂ * (a/c + c/a) + d₃ * (a/b + b/a) := by
    rw [show d₁ * (b/c + c/b) + d₂ * (a/c + c/a) + d₃ * (a/b + b/a) = (d₂ * (c/a) + d₃ * (b/a)) + (d₃ * (a/b) + d₁ * (c/b)) + (d₁ * (b/c) + d₂ * (a/c)) by ring]
    linarith
  have h_geom1 : 2 ≤ b/c + c/b := add_div_self_ge_two hb hc
  have h_geom2 : 2 ≤ a/c + c/a := add_div_self_ge_two ha hc
  have h_geom3 : 2 ≤ a/b + b/a := add_div_self_ge_two ha hb
  nlinarith

/-- The Erdős-Mordell Theorem: R₁ + R₂ + R₃ ≥ 2 * (d₁ + d₂ + d₃). -/
theorem erdos_898 {A B C P : V} (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    dist P A + dist P B + dist P C ≥ 2 * (dist_to_line P B C + dist_to_line P A C + dist_to_line P A B) := by
  let a := dist B C; let b := dist A C; let c := dist A B
  have h_ne_BC : B ≠ C := by intro h; subst h; apply h_triangle; rw [show ({A, B, B} : Set V) = {A, B} by ext x; simp]; apply collinear_pair
  have h_ne_AC : A ≠ C := by intro h; subst h; apply h_triangle; rw [show ({A, B, A} : Set V) = {A, B} by ext x; simp; tauto]; apply collinear_pair
  have h_ne_AB : A ≠ B := by intro h; subst h; apply h_triangle; rw [show ({A, A, C} : Set V) = {A, C} by ext x; simp]; apply collinear_pair
  have ha : 0 < a := dist_pos.mpr h_ne_BC
  have hb : 0 < b := dist_pos.mpr h_ne_AC
  have hc : 0 < c := dist_pos.mpr h_ne_AB

  have h_tri_perm1 : ¬ Collinear ℝ ({B, C, A} : Set V) := by rwa [show ({B, C, A} : Set V) = {A, B, C} by ext x; simp; tauto]
  have h_tri_perm2 : ¬ Collinear ℝ ({C, A, B} : Set V) := by rwa [show ({C, A, B} : Set V) = {A, B, C} by ext x; simp; tauto]

  have h_int_perm1 : P ∈ interior (convexHull ℝ ({B, C, A} : Set V)) := by rwa [show ({B, C, A} : Set V) = {A, B, C} by ext x; simp; tauto]
  have h_int_perm2 : P ∈ interior (convexHull ℝ ({C, A, B} : Set V)) := by rwa [show ({C, A, B} : Set V) = {A, B, C} by ext x; simp; tauto]

  have h1 := erdos_898_lemma h_triangle h_interior
  have h2 := erdos_898_lemma h_tri_perm1 h_int_perm1
  have h3 := erdos_898_lemma h_tri_perm2 h_int_perm2

  apply erdos_898_summation (dist P A) (dist P B) (dist P C)
    (dist_to_line P B C) (dist_to_line P A C) (dist_to_line P A B)
    a b c ha hb hc dist_nonneg dist_nonneg dist_nonneg
  · exact h1
  · convert h2 using 1; simp [a, b, c, dist_to_line, dist_comm, Set.pair_comm]
  · convert h3 using 1; simp [a, b, c, dist_to_line, dist_comm, Set.pair_comm]

end

#print axioms erdos_898
-- 'Erdos898.erdos_898' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos898
